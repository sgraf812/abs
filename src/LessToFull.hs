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
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DuplicateRecordFields     #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeApplications          #-}

module LessToFull (Bijection, forward, backward) where

import Prelude
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
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import GHC.Stack

import Expr
import qualified Stateless
import qualified Stackless
import qualified Envless
import qualified DynamicEnv
import qualified Stateful

type LessD = Stateless.D
type FullD = Stateful.D
data Cache = C
  { fw_init_trace :: !(CallStack -> Trace LessD -> Trace FullD)
  , bw_init_trace :: !(CallStack -> Trace FullD -> Trace LessD)
  }

key :: HasLabel (StateX d) => Trace d -> (Label, Int)
key p = (labelOf (src p), lenT p)

memo :: a -> IO Cache
memo x = do
  ref <- newIORef (Map.empty, Map.empty)
  let cache :: Cache
      cache = x `seq` C fw_init_trace bw_init_trace
      fw_init_trace :: CallStack -> Trace LessD -> Trace FullD
      fw_init_trace cs p = unsafePerformIO $ do
        (fwt,bwt) <- readIORef ref
        let k = key p
        --traceM ("fw_init_trace " ++ show p)
        case Map.lookup k fwt of
          Just sp' -> return sp'
          Nothing  -> do
            let ?callStack = cs
            let sp' = forward' cache p
            let !fwt' = Map.insert k sp' fwt
            writeIORef ref (fwt',bwt)
            return sp'
      bw_init_trace :: CallStack -> Trace FullD -> Trace LessD
      bw_init_trace cs sp = unsafePerformIO $ do
        (fwt,bwt) <- readIORef ref
        let k = key sp
        --traceM ("bw_init_trace " ++ show (tgt sp) ++ "{")
        case Map.lookup k bwt of
          Just p' -> return p'
          Nothing  -> do
            let ?callStack = cs
            let p' = backward' cache sp
            --traceM ("no} " ++ show p')
            let !bwt' = Map.insert k p' bwt
            writeIORef ref (fwt,bwt')
            return p'
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
cachedForwardTrace c = fw_init_trace c callStack

cachedBackwardTrace :: HasCallStack => Cache -> Trace FullD -> Trace LessD
cachedBackwardTrace c = bw_init_trace c callStack

traceWrap :: String -> (a -> String) -> (b -> String) -> (a -> b) -> a -> b
--traceWrap hdr bef af f x = trace (hdr ++ " (" ++ bef x ++ ") {") $ traceWith (\(!r) -> "} (" ++ af r ++ ")") $ f x
traceWrap hdr bef af f x = f x

instance Bijection LessD FullD where
  forward'  cache (Stateless.D d) = Stateful.D  $ \sp ->
    let p = traceWrap "backward' @Trc, init" (\p -> show (tgt p)) (\p -> show (tgt p)) (cachedBackwardTrace cache) . tgtInv $ sp
    in dropT (lenT p) . traceWrap "foward' @Trc, cont" (\p -> show (src p)) (\p -> show (tgt p)) (forward' cache) . concatT p . d $ p
    -- It is vital not to force the result of d deeply
    -- because that destroys productivity of d!
  backward' cache (Stateful.D d)  = Stateless.D $ traceWrap "backward' @Trc, cont" (\p -> show (src p, tgt p)) (\p -> show (tgt p)) (backward' cache) . d . tgt' . traceWrap "foward' @Trc, init" (\p -> show (tgt p)) (\p -> show (tgt p)) (cachedForwardTrace cache)

instance Bijection Stateless.Value Stateful.Value where
  forward'  cache (Stateless.Fun f) = Stateful.Fun (traceWrap "foward' @D" (\p -> "") (\p -> "") (forward' cache)  . f . Stateless.deref')
  backward' cache (Stateful.Fun f) = Stateless.Fun (traceWrap "backward' @D" (\p -> "") (\p -> "") (backward' cache) . f . Stateless.derefInv)

forward_state :: Cache -> Trace LessD -> Stateful.State
forward_state cache p = (fw_ctrl p (tgt p), fw_env (Stateless.materialiseEnv p), fw_heap p (Stateless.materialiseHeap' p), fw_stack [] p)
  where
    fw_ctrl :: Trace LessD -> ProgPoint LessD -> ProgPoint FullD
    fw_ctrl p (Ret _) = Ret (sv,forward' cache v) where Just (E sv, v) = valT p
    fw_ctrl p (E le)  = E le

    fw_env :: Env (SIAddr, LessD) -> Env Addr
    fw_env = Map.map Stateless.derefInv

    fw_heap :: Trace LessD -> (Addr :-> (LExpr, LessD)) -> Stateful.Heap
    fw_heap p = Map.mapWithKey (\a (le, d) -> (le, fw_env $ Stateless.materialiseEnvForAddr p a, Stateful.D $ \p -> Stateful.unD (forward' cache d) p ))

    fw_stack :: Stateful.Cont -> Trace LessD -> Stateful.Cont
    fw_stack stk (End _) = stk
    fw_stack stk (SnocT p a _) = case a of
      LookupA ui -> Stateful.Update ui.addr : fw_stack stk p
      App1A ai -> Stateful.Apply (Stateless.derefInv ai.arg1) : fw_stack stk p
      UpdateA ui
        | Stateful.Update a:stk <- fw_stack stk p, a == ui.addr -> stk
        | otherwise -> error ("Could not pop " ++ show ui.addr)
      App2A ai
        | Stateful.Apply a:stk <- fw_stack stk p, a == Stateless.derefInv ai.arg -> stk
        | otherwise -> error ("Could not pop " ++ show (Stateless.derefInv ai.arg))
      _ -> fw_stack stk p
    fw_stack stk (ConsT _ a p) = case a of
      LookupA ui -> fw_stack (Stateful.Update ui.addr : stk) p
      App1A ai -> fw_stack (Stateful.Apply (Stateless.derefInv ai.arg1) : stk) p
      UpdateA ui
        | Stateful.Update a:stk' <- stk, a == ui.addr -> stk'
        | otherwise -> error ("Could not pop " ++ show ui.addr)
      App2A ai
        | Stateful.Apply a:stk' <- stk, a == Stateless.derefInv ai.arg -> stk'
        | otherwise -> error ("Could not pop " ++ show (Stateless.derefInv ai.arg))
      _ -> fw_stack stk p

forward_action :: HasCallStack => Cache -> ProgPoint LessD -> Action LessD -> ProgPoint LessD -> Action FullD
forward_action cache _ a _ = case a of
  ValA{} -> ValA NI
  UpdateA ui -> UpdateA ui
  LookupA li -> LookupA li
  BindA bi -> BindA (bi { denot = Stateful.D $ traceWrap ("forward_action BindA " ++ show a) (\sp -> "") (\sp' -> "") (Stateful.unD (forward' cache bi.denot)) })
  App1A ai -> App1A (A1I (Stateless.derefInv ai.arg1))
  App2A ai -> App2A (ai { arg = Stateless.derefInv ai.arg })

assert_init_trace p = assertMsg (labelOf (src p) == 1) ("Not an initialisation trace: " ++ show p) p

instance Bijection (Trace LessD) (Trace FullD) where
  forward' cache = mapTraceWithPrefixes (forward_state cache) (forward_action cache) . assert_init_trace
  backward' cache = mapTraceWithPrefixes forget_ret (backward_action cache)
    where
      forget_ret sp | (c,_,_,_) <- tgt sp = mapProgPoint (const NI) c
      backward_action :: Cache -> Stateful.State -> Action FullD -> Stateful.State -> Action LessD
      backward_action cache _ a q = case a of
        ValA _ | (Ret (sv,v),_,_,_) <- q -> ValA (backward' cache v)
        UpdateA ui -> UpdateA ui
        LookupA li -> LookupA li
        BindA bi -> BindA (bi { denot = Stateless.D $ traceWrap ("backward_action BindA " ++ show a) (\p -> "") (\p' -> "") (Stateless.unD (backward' cache bi.denot)) })
        App1A ai -> App1A (A1I (Stateless.deref' ai.arg1))
        App2A ai -> App2A (ai { arg = (Stateless.deref' ai.arg) })

