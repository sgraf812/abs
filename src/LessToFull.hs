{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

module LessToFull (Bijection, forward, backward) where

import Prelude hiding (forward')
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Text.Show (showListWith)

import Expr
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import GHC.Stack

import qualified Stateless
import qualified Stackless
import qualified Envless
import qualified DynamicEnv
import qualified Stateful
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

type LessD = Stateless.D
type FullD = Stateful.D
data Cache = C
  { fw_trace :: CallStack -> Trace LessD -> Trace FullD
  , bw_trace :: CallStack -> Trace FullD -> Trace LessD
  , fw_expr  :: CallStack -> LExpr -> LessD -> FullD
  , bw_expr  :: CallStack -> LExpr -> FullD -> LessD
  }

key :: HasLabel (StateX d) => Trace d -> (Label, Int)
key p = (labelOf (src p), lenT p)

memo :: a -> IO Cache
memo x = do
  ref <- newIORef (Map.empty, Map.empty, Map.empty, Map.empty)
  let cache :: Cache
      cache = x `seq` C fw_trace bw_trace fw_expr bw_expr
      fw_trace :: CallStack -> Trace LessD -> Trace FullD
      fw_trace cs p = unsafePerformIO $ do
        (fwt,bwt,fwe,bwe) <- readIORef ref
        let k = key p
        case Map.lookup k fwt of
          Just sp -> return sp
          Nothing -> do
            let ?callStack = cs
            let sp = forward' cache p
            let !fwt' = Map.insert k sp fwt
            writeIORef ref (fwt', bwt,fwe,bwe)
            return sp
      bw_trace :: CallStack -> Trace FullD -> Trace LessD
      bw_trace cs sp = unsafePerformIO $ do
        (fwt,bwt,fwe,bwe) <- readIORef ref
        let k = key sp
        case Map.lookup k bwt of
          Just p -> return p
          Nothing -> do
            let ?callStack = cs
            let p = backward' cache sp
            let !bwt' = Map.insert k p bwt
            writeIORef ref (fwt, bwt',fwe,bwe)
            return p
      fw_expr :: CallStack -> LExpr -> LessD -> FullD
      fw_expr cs le d = unsafePerformIO $ do
        (fwt,bwt,fwe,bwe) <- readIORef ref
        let k = labelOf le
        case Map.lookup k fwe of
          Just sp -> return sp
          Nothing  -> do
            let ?callStack = cs
            let sd = forward' cache d
            let !fwe' = Map.insert k sd fwe
            writeIORef ref (fwt, bwt,fwe',bwe)
            return sd
      bw_expr :: CallStack -> LExpr -> FullD -> LessD
      bw_expr cs le sd = unsafePerformIO $ do
        (fwt,bwt,fwe,bwe) <- readIORef ref
        let k = labelOf le
        case Map.lookup k bwe of
          Just d -> return d
          Nothing  -> do
            let ?callStack = cs
            let d = backward' cache sd
            let !bwe' = Map.insert k d bwe
            writeIORef ref (fwt, bwt,fwe,bwe')
            return d
  return cache
{-# NOINLINE memo #-}

forward :: HasCallStack => Bijection from to => from -> to
forward from = forward' (unsafePerformIO (memo from)) from

backward :: Bijection from to => to -> from
backward to = backward' (unsafePerformIO (memo to)) to

class Bijection from to | from -> to, to -> from where
  forward' :: HasCallStack => Cache -> from -> to
  backward' :: HasCallStack => Cache -> to -> from


-----------------------------------------------
--                                           --
--          Stateless to Stateful          --
--                                           --
-----------------------------------------------

-- Problems:
--   1. Less[x]_ρ = Less[y]_ρ iff ρ(x) = ρ(y).
--      By constrast, Full[x](σ) /= σ. => Full[y](σ) = σ.
--      But arguably that is a stronger property than we actually need.
--      We could fix that in Full by matching on the same address instead of
--      same variable, lookAddr instead of look.
--      Or on the Less side, we could require ρ to also take the ProgPoint from where to start.
--

type StatelessEnv = Env (SIAddr, LessD)

cachedForwardTrace :: HasCallStack => Cache -> Trace LessD -> Trace FullD
cachedForwardTrace c = fw_trace c callStack

cachedBackwardTrace :: HasCallStack => Cache -> Trace FullD -> Trace LessD
cachedBackwardTrace c = bw_trace c callStack

cachedForwardD :: HasCallStack => Cache -> LExpr -> LessD -> FullD
cachedForwardD c = fw_expr c callStack

cachedBackwardD :: HasCallStack => Cache -> LExpr -> FullD -> LessD
cachedBackwardD c = bw_expr c callStack

instance Bijection LessD FullD where
  forward'  cache (Stateless.D d) = Stateful.D  $ \sp ->
    let p = cachedBackwardTrace cache . tgtInv $ sp
    in dropT (lenT p) . forward' cache . concatT p . d $ p
    -- It is vital not to call cachedForwardTrace on the result of d, because it
    -- forces the result deeply, destroying productivity of d!
  backward' cache (Stateful.D d)  = Stateless.D $ backward' cache . d . tgt' . cachedForwardTrace cache
--    .
instance Bijection Stateless.Value Stateful.Value where
  forward'  cache (Stateless.Fun f) = Stateful.Fun (forward' cache  . f . Stateless.deref')
  backward' cache (Stateful.Fun f) = Stateless.Fun (backward' cache . f . Stateless.derefInv)

forward_state :: Cache -> Trace LessD -> Stateful.State
forward_state cache p = (fw_ctrl p (tgt p), fw_env (Stateless.materialiseEnv p), fw_heap p (Stateless.materialiseHeap' p), fw_stack p)
  where
    fw_ctrl :: Trace LessD -> ProgPoint LessD -> ProgPoint FullD
    fw_ctrl p (Ret _) = Ret (sv,forward' cache v) where Just (E sv, v) = valT p
    fw_ctrl p (E le)  = E le

    fw_env :: Env (SIAddr, LessD) -> Env Addr
    fw_env = Map.map Stateless.derefInv

    fw_heap :: Trace LessD -> (Addr :-> (LExpr, LessD)) -> Stateful.Heap
    fw_heap p = Map.mapWithKey (\a (le, d) -> (le, fw_env $ Stateless.materialiseEnvForAddr p a, cachedForwardD cache le d))

    fw_stack :: Trace LessD -> Stateful.Cont
    fw_stack (End _) = []
    fw_stack (SnocT p a _) = case a of
      LookupA ui -> Stateful.Update ui.addr : fw_stack p
      App1A ai -> Stateful.Apply (useSemanticallyIrrelevant $ fst ai.arg1) : fw_stack p
      _ -> fw_stack p

forward_action :: HasCallStack => Cache -> ProgPoint LessD -> Action LessD -> ProgPoint LessD -> Action FullD
forward_action cache _ a _ = case a of
  ValA{} -> ValA NI
  UpdateA ui -> UpdateA ui
  LookupA li -> LookupA li
  BindA bi -> BindA (bi { denot =  cachedForwardD cache bi.rhs bi.denot })
  App1A ai -> App1A (A1I (Stateless.derefInv ai.arg1))
  App2A ai -> App2A (ai { arg = Stateless.derefInv ai.arg })

instance Bijection (Trace LessD) (Trace FullD) where
  forward' cache = mapTraceWithPrefixes (forward_state cache) (forward_action cache)
  backward' cache = mapTraceWithPrefixes forget_ret (backward_action cache)
    where
      forget_ret sp | (c,_,_,_) <- tgt sp = mapProgPoint (const NI) c
      backward_action :: Cache -> Stateful.State -> Action FullD -> Stateful.State -> Action LessD
      backward_action cache _ a q = case a of
        ValA _ | (Ret (_,v),_,_,_) <- q -> ValA (backward' cache v)
        UpdateA ui -> UpdateA ui
        LookupA li -> LookupA li
        BindA bi -> BindA (bi { denot = cachedBackwardD cache bi.rhs bi.denot })
        App1A ai -> App1A (A1I (Stateless.deref' ai.arg1))
        App2A ai -> App2A (ai { arg = (Stateless.deref' ai.arg) })

