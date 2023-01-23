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

module Cont (C(..), maxinf, absD, concD) where

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
import qualified Direct

import Expr
import ByNeed

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
         in unC (step App1A le.at (go le env)) p (k . apply)
      Lam n le ->
        let val = Fun (\c -> step App2A (le.at) (go le (Map.insert n c env)))
         in C $ \_p k -> k (ConsT le.at (ValA val) (End le.after))
      Let n le1 le2 -> C $ \p ->
        let c = step (LookupA p) le1.at (go le1 env')
            env' = Map.insert n c env
         in unC (step BindA le2.at (go le2 env')) p

-- | As Reynolds first proved in "On the relation between Direct and
-- Continuation Semantics", we have `concD . absD = id`. In our case,
-- parametricity also gives us `absD . concD = id` by the following
-- observation:
--
-- Observation: By parametricity, any `c::C` must be of the form
-- `\p k -> k (f p)` for some `f::Trace C -> Trace C`.
--
-- First off, two lemmas about trace abstraction and botE and botD:
--  1. concTrace.botE.absTrace = unD botD
--  2. absTrace.unD botD.concTrace = botE
--
-- Equipped with that knowledge, we can proceed by well-founded induction over
-- By well-founded induction over the domain C.
--
-- Here is the proof for n=0:
--   concD(absD botD)
-- = concD(C $ \p k -> k . absTrace . unD botD . concTrace $ p)
-- = concD(C $ \p k -> k (botE p))
-- = botC
--
--   absD(concD botC)
-- = absD(concD (C (\p k -> k (botE p))))
-- = C $ \p k -> k $ absTrace (concTrace (botE (absTrace (concTrace p))))
-- = C $ \p k -> k $ absTrace (unD botD (concTrace p))  { lemma (1) }
-- = C $ \p k -> k $ botE p                             { lemma (2) }
-- = botC
--
-- For the inductive step, assume that The recursive calls to (absD . concD)
-- (concD . absD) have been show to be id for universe levels lower than the
-- current one n+1.
--
-- concD(absD (D d))
-- = concD (C $ \p k -> k . absTrace . d . concTrace $ p)
-- = D $ \p -> (\p k -> k . absTrace . d . concTrace $ p) (absTrace p) concTrace
-- = D $ \p -> concTrace . absTrace . d . concTrace . absTrace $ p
--   { apply IH, get (concTrace . absTrace = id) for sub-terms }
-- = D $ \p -> id . d . id $ p
-- = D d
--
-- absD(concD c)
-- = absD(concD (C (\p k -> k (f p))))    { parametricity }
-- = absD(D $ \p -> (\p k -> k (f p)) (absTrace p) concTrace)
-- = absD(D $ \p -> concTrace (f (absTrace p)))
-- = C $ \p k -> k . absTrace . (\p -> concTrace (f (absTrace p))) . concTrace $ p
-- = C $ \p k -> k $ absTrace (concTrace (f (absTrace (concTrace p))))
--   { apply IH, get (absTrace . concTrace = id) for sub-terms }
-- = C $ \p k -> k $ id (f (id p))
-- = C $ \p k -> k (f p)
-- = c
absD :: Direct.D -> Cont.C
absD (Direct.D d) = Cont.C $ \p k -> k . absTrace . d . concTrace $ p

concD :: Cont.C -> Direct.D
concD (Cont.C c) = Direct.D $ \p -> c (absTrace p) concTrace

absValue :: Value Direct.D -> Value Cont.C
absValue (Fun f) = Fun (absD . f . concD)

absAction :: Action Direct.D -> Action Cont.C
absAction = dimapAction absD concD

concAction :: Action Cont.C -> Action Direct.D
concAction = dimapAction concD absD

-- | (Inductive) Assumption: (absD . concD = id), (concD . absD = id)
--
--   absTrace (concTrace p)
-- = dimapTrace absD concD (dimapTrace concD absD p)
-- = dimapTrace (absD . concD) (concD . absD) p
-- = dimapTrace id id p
-- = p
absTrace :: Trace Direct.D -> Trace Cont.C
absTrace = dimapTrace absD concD

concTrace :: Trace Cont.C -> Trace Direct.D
concTrace = dimapTrace concD absD
