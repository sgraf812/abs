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

-- | Finite intialisation trace to infinite or maximal finite trace.
--
-- This type is actually the subtype of `Trace -> Trace` for which every
-- inhabitant `d` satisfies `src(d(p)) = dst(p)`.
--
-- We can give a partial pointwise prefix order ⊑:
--
-- d1(p) ⊑ d2(p)  <=>  ∃p'. d1(p) `concatT` p' = d2(p)
--
-- Note that a `D` is *not* a monotone map; indeed our semantics isn't.
-- The ordering is to be understood pointwise, ⊑^. .
--
-- There exists a bottom element `⊥(p) = End (dst p)` and directed sets have a
-- the pointwise supremum ⊔^.
-- (Finite case is simply the max element; infinite case is the limit of the
-- prefix traces).
-- Thus, (D,⊑^.,⊥,⊔^.) forms a CPO with bottom element ⊥.
-- Note that ⊥ represents an expression that is stuck in every context;
-- values do at least another step in our semantics.
--
newtype D = D { unD :: Trace D -> Trace D }

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End (dst p))

-- | The partial pointwise prefix order. Can't compute :(
leqD :: D -> D -> Bool
leqD d1 d2 = forall (\p -> unD d1 p `isPrefixOf` unD d2 p)
  where
    forall f = undefined -- would need to iterate over all Traces
    t1 `isPrefixOf` t2 = case (consifyT t1, consifyT t2) of
      (End l, ConsT l' _ _) -> l == l'
      (ConsT l _ t, ConsT l' _ t') -> l == l' && t1 `isPrefixOf` t2
      (_,_) -> False

-- | The pairwise lub on ordered `D`s. Undefined everywhere else
lubD :: D -> D -> D
lubD d1 d2 = if d1 `leqD` d2 then d2 else d1

instance Eq D where
  _ == _ = True

instance Ord D where
  compare _ _ = EQ

instance Show D where
  show _ = "D"

step :: Action D -> Label -> D -> D
step a l sem = D $ \p -> ConsT (dst p) a $ unD sem $ SnocT p a l

(!⊥) :: Ord a => (a :-> D) -> a -> D
env !⊥ x = Map.findWithDefault botD x env

maxinf :: LExpr -> (Name :-> D) -> Trace D -> Trace D
maxinf le env p
  | dst p /= le.at = unD botD p -- stuck. act as bottom! Only happens on the initial call, I guess???
                                -- In all other cases we go through the step function.
  | otherwise      = unD (go le env) p
  where
    go :: LExpr -> (Name :-> D) -> D
    go le !env = case le.thing of
      Var n -> env !⊥ n
      App le n -> D $ \p ->
        let p2 = unD (step (AppA n) le.at (go le env)) p
         in concatT p2 $ case val p2 of
              Just (Fun f) -> unD (f (env !⊥ n)) (concatT p p2)
              Nothing      -> undefined -- actually Bottom! Can't happen in a closed
                                        -- program without Data types, though
      Lam n le ->
        let val = Fun (\d -> step (BetaA n) (le.at) (go le (Map.insert n d env)))
         in D $ \_ -> ConsT le.at (ValA val) (End le.after)
      Let n le1 le2 ->
        let d = step LookupA le1.at (go le1 env')
            env' = Map.insert n d env
         in step (BindA n le1.at d) le2.at (go le2 env')

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
post :: LExpr -> D -> Trace D -> Label -> [Configuration]
post le d p l = map (config (unlabel le) . concatT p) (tracesAt l (unD d p))
