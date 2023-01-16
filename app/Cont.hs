{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}

module Cont (maxinf) where

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
import ByName

newtype C = C { unC :: forall r. Trace C -> (Trace C -> r) -> r }
type E = Trace C -> Trace C

botE :: E
botE p = End (dst p)

instance Eq E where
  _ == _ = True

instance Ord E where
  compare _ _ = EQ

instance Show E where
  show _ = "E"

instance Show C where
  show _ = "C"

--step :: Action C -> Label -> C -> C
--step a l sem = C $ \k -> unC sem (k . (\e p -> ConsT (dst p) a (e (SnocT p a l))))

step :: Action C -> Label -> C -> C
step a l sem = C $ \p k -> unC sem (SnocT p a l) (k . ConsT (dst p) a)

(!⊥) :: Ord a => (a :-> C) -> a -> C
env !⊥ x = Map.findWithDefault (C $ \p k -> k (botE p)) x env

maxinf :: LExpr -> (Name :-> C) -> Trace C -> Trace C
maxinf le env p
  | dst p /= le.at = botE p -- stuck. act as bottom! Only happens on the initial call, I guess???
                                -- In all other cases we go through the step function.
  | otherwise      = unC (go le env) p id
  where
    traceP :: C -> C
    traceP c = C $ \p k -> traceShow p $ unC c p k
    go :: LExpr -> (Name :-> C) -> C
    go le !env = case le.thing of
      Var n -> env !⊥ n
      App le n -> C $ \p k ->
        let apply p2 =
              case val p2 of
                    Just (Fun f) -> unC (f (env !⊥ n)) (concatT p p2) (concatT p2)
                    Nothing      -> undefined -- actually Bottom! Can't happen in a closed
                                              -- program without Data types, though
         in unC (step (AppA n) le.at (go le env)) p (k . apply)
      Lam n le ->
        let val = Fun (\c -> step (BetaA n) (le.at) (go le (Map.insert n c env)))
         in C $ \_p k -> k (ConsT le.at (ValA val) (End le.after))
      Let n le1 le2 ->
        let c = step LookupA le1.at (go le1 env')
            env' = Map.insert n c env
         in step (BindA n le1.at c) le2.at (go le2 env')

-- post(go le []) will be the reachability semantics, e.g., small-step!
-- Wart: Instead of a (set of) Trace `t`, it should take a (set of) Configuration `c`
-- such that `config p = c` (that is, we don't know how to efficiently compute
-- the concretisation function γ(cs) = ts). By doing it this way, we can
-- actually compute.
-- The lifting to sets (of initialisation Traces/Configurations) is routine.
-- we return a list instead of a set, because it might be infinite and we want to
-- enumerate.
--
-- Note that we never look at the `Expr` returned by the indexing function.
--post :: LExpr -> E -> Trace E -> Label -> [Configuration]
--post le d p l = map (config (unlabel le) . concatT p) (tracesAt l (unE d p))
