{-# LANGUAGE BangPatterns #-}
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
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}

module LessToFull (GaloisAbstraction(..)) where

import Prelude hiding (abs)
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

class GaloisAbstraction from to where
  abs :: from -> to
  conc :: to -> from


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

type StatelessEnv = Env (Stateless.SIAddr, Stateless.D)

concEnv :: Stateful.State -> StatelessEnv
concEnv (_,env,_,_) = Map.map (\a -> (SI a, conc (Stateful.alternativeVar a))) env

absEnv :: StatelessEnv -> Env Addr
absEnv = Map.map (useSemanticallyIrrelevant . fst)

--instance GaloisAbstraction (StatelessEnv -> Stateless.D) Stateful.D where
--  abs  f = Stateful.D $ \(SI p) s -> assert (labelOf s == labelOf (dst p)) $ abs (Stateless.unD (f (concEnv s)) (conc p))
--  conc (Stateful.D d) env = Stateless.D $ \p -> let p' = abs p in conc (d (SI p') (dst p'))

instance GaloisAbstraction Stateless.D Stateful.D where
  abs  (Stateless.D d) = Stateful.D  $ \(SI p) s -> assert (labelOf s == labelOf (dst p)) $ abs (d (conc p))
  conc (Stateful.D d)  = Stateless.D $ \p -> let p' = abs p in conc (d (SI p') (dst p'))

instance GaloisAbstraction Stateless.Value Stateful.Value where
  abs  (Stateless.Fun f) = Stateful.Fun (\a -> Stateful.D $ \p s -> Stateful.unD (abs (f (SI a,conc (Stateful.alternativeVar a)))) p s)
  conc (Stateful.Fun f) = Stateless.Fun (\(SI a,_) -> conc (f a))

--instance GaloisAbstraction (Trace Stateless.D) Stateful.State where
--  abs  p = dst (abs p :: Trace Stateful.D)
--  conc (p, env, heap, stk) = prep_cont stk $ prep_heap (Map.toList heap) $ End (mapProgPoint (const NI) p)
--    where
--      dummyLabel = -1
--      dummy_p = E (Lab dummyLabel (Var "x"))
--      prep_heap ((a,(e,d)):rest) inner =
--        prep_heap rest (ConsT dummy_p (BindA (BI "x" e a (conc d)) :: Action Stateless.D) inner)
--      prep_cont (Stateful.Update a:rest) inner =
--        ConsT dummy_p (LookupA (LI a) :: Action Stateless.D) (prep_cont rest inner)
--      prep_cont (Stateful.Apply d:rest) inner =
--        ConsT dummy_p (App1A (A1I (conc d)) :: Action Stateless.D) (prep_cont rest inner)

instance GaloisAbstraction (Trace Stateless.D) (Trace Stateful.D) where
  abs p = go Map.empty Map.empty Map.empty (toList (splitsT p))
    where
      mk_state_at :: ProgPoint Stateless.D -> Trace Stateless.D -> Env Addr -> Stateful.Heap -> Stateful.State
      mk_state_at p pref env heap
        | Ret NI <- p, let Just (E sv,v) = valT pref
        = (Ret (sv, abs v), env, heap, mk_cont pref)
        | E e <- p
        = (E e, env, heap, mk_cont pref)
      mk_cont :: Trace Stateless.D -> Stateful.Cont
      mk_cont (End _) = []
      mk_cont (ConsT _ act t) = case act of
        LookupA a -> Stateful.Update a.addr : mk_cont t
        App1A d   -> Stateful.Apply (useSemanticallyIrrelevant $ fst d.arg1) : mk_cont t
        _         -> mk_cont t

      go :: (Addr :-> StatelessEnv) -> StatelessEnv -> Stateful.Heap -> [(Trace Stateless.D,Trace Stateless.D)] -> Trace Stateful.D
      go envs env heap ((pref,suff):rest) = case suff of
        End l -> End (mk_state_at l pref (absEnv env) heap)
        ConsT l a p -> ConsT (mk_state_at l pref (absEnv env) heap) a' $ case a of
          BindA bi ->
            let env' = Map.insert bi.name (SI bi.addr, bi.denot) env
                envs' = Map.insert bi.addr env' envs
                heap' = Map.insert bi.addr (bi.rhs, abs bi.denot :: Stateful.D)
             in go envs' env' heap rest
          LookupA a -> go envs (envs Map.! a.addr) heap rest
          UpdateA a ->
            let Just (E sv,v) = valT pref
                d = Stateless.wrapLookup a.addr (E sv) (Stateless.step (ValA v) (Ret NI))
             in go (Map.insert a.addr env envs) env (Map.insert a.addr (sv, (absEnv env), abs d) heap) rest
          ValA v ->
            go envs env heap rest
          App1A _ ->
            go envs env heap rest
          App2A ai ->
            go envs (Map.insert ai.name ai.arg env) heap rest
          where
            a' = case a of
              ValA{} -> ValA NI
              UpdateA ui -> UpdateA ui
              LookupA li -> LookupA li
              BindA bi -> BindA (bi { denot = abs bi.denot })
              App1A ai -> App1A (A1I (useSemanticallyIrrelevant $ fst $ ai.arg1))
              App2A ai -> App2A (ai { arg = useSemanticallyIrrelevant $ fst $ ai.arg })

  conc t = go t
    where
      forget_ret = mapProgPoint (const NI)
      go (End (p,_,_,_)) = End (forget_ret p)
      go (ConsT (p,_,_,_) a rest) =
        ConsT (forget_ret p) a' (go rest)
          where
            a' = case a of
              ValA _ | (Ret (_,v),_,_,_) <- src rest -> ValA (conc v)
              UpdateA ui -> UpdateA ui
              LookupA li -> LookupA li
              BindA bi -> BindA (bi { denot = conc bi.denot })
              App1A ai -> App1A (A1I (SI ai.arg1, conc (Stateful.alternativeVar ai.arg1)))
              App2A ai -> App2A (ai { arg = (SI ai.arg, conc (Stateful.alternativeVar ai.arg)) })

