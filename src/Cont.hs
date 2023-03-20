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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cont (C(..), maxinf, absD, concD, absTrace, concTrace) where

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

type instance AddrOrD C = C
data instance Value C = CFun (C -> C)

newtype C = C { unC :: (Trace C -> Trace C) -> Trace C -> Trace C }

botC :: C
botC = C $ \k p -> k (End (dst p))

instance Show C where
  show _ = "C"

step :: Action C -> Label -> C
step a l = C $ \k p -> ConsT (dst p) a $ k $ SnocT p a l

stepRet :: Action C -> C
stepRet a = C $ \k p ->
  if dst p /= returnLabel
    then k p
    else ConsT returnLabel a $ k $ SnocT p a returnLabel

whenAtP :: Label -> C -> C
whenAtP l c = askP $ \p -> if l == dst p then c else botC

memo :: Addr -> Label -> C -> C
memo a l sem = askP $ \pi ->
  let (l', d) = case update a (snocifyT pi) of
        Just (l', v) -> (l', step (ValA v) returnLabel)
        Nothing      -> (l, sem)
      update addr (SnocT pi' a _)
        | UpdateA addr' <- a
        , addr == addr'
        = valT pi'
        | otherwise  = update addr pi'
      update _ End{} = Nothing
  in step (LookupA a) l' <++> d <++> whenAtP returnLabel (step (UpdateA a) returnLabel)

--memo :: Addr -> C -> C
--memo addr sem = askP $ \pi -> case lookup (snocifyT pi) of
--  Just pv -> C $ \k p -> pv `concatT` k (rewrite p (src pv) `concatT` pv)
--  Nothing -> sem
--  where
--    rewrite (SnocT p a@LookupA{} _l) l = SnocT p a l
--    lookup (SnocT p a _)
--      | UpdateA addr' <- a
--      , addr == addr'
--      = valT p
--      | otherwise = lookup p
--    lookup (End l) = Nothing

(>->) :: Action C -> Label -> C
a >-> l = step a l
infix 7 >->

concatC :: C -> C -> C
concatC (C c1) (C c2) = C $ c1 . c2
-- = C $ \k -> c1 (c2 k)
-- = C $ \k p -> c1 (c2 k) p
infixr 5 `concatC`

(<++>) :: C -> C -> C
(<++>) = concatC
infixr 5 <++>

instance Semigroup C where
  (<>) = (<++>)

instance Monoid C where
  mempty = C $ \k p -> k p

askP :: (Trace C -> C) -> C
askP f = C $ \k p -> unC (f p) k p

(!⊥) :: Ord a => (a :-> C) -> a -> C
env !⊥ x = Map.findWithDefault botC x env

maxinf :: LExpr -> (Name :-> C) -> Trace C -> Trace C
maxinf le env p
  | dst p /= le.at = unC botC id p
  | otherwise      = unC (go le env) (End . dst) p
  where
    go :: LExpr -> (Name :-> C) -> C
    go le !env = case le.thing of
      Var n -> env !⊥ n
      App le n ->
        case Map.lookup n env of
          Just d ->
            let apply = askP $ \p -> case val p of
                  Just (CFun f) -> f d
                  Nothing      -> botC
             in step App1A le.at <++> go le env <++> apply
          Nothing -> botC
      Lam n le' ->
        let val = CFun (\c -> App2A n c >-> le'.at <++> go le' (Map.insert n c env))
         in step (ValA val) returnLabel
      Let n le1 le2 -> askP $ \p ->
        let a = hash p
            c = memo a le1.at (go le1 env')
            env' = Map.insert n c env
         in step (BindA n a c) le2.at <++> go le2 env'

-- | As Reynolds first proved in "On the relation between Direct and
-- Continuation Semantics", we have `concD . absD = id`. In our case,
-- parametricity also gives us `absD . concD = id` by the following
-- observation:
--
-- Observation: By parametricity, any `c::C` must be of the form
-- `\k p -> k (f p)` for some `f::Trace C -> Trace C`.
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
-- = concD(C $ \k p -> k . absTrace . unD botD . concTrace $ p)
-- = concD(C $ \k p -> k (botE p))
-- = botC
--
--   absD(concD botC)
-- = absD(concD (C (\k p -> k (botE p))))
-- = C $ \k p -> k $ absTrace (concTrace (botE (absTrace (concTrace p))))
-- = C $ \k p -> k $ absTrace (unD botD (concTrace p))  { lemma (1) }
-- = C $ \k p -> k $ botE p                             { lemma (2) }
-- = botC
--
-- For the inductive step, assume that The recursive calls to (absD . concD)
-- (concD . absD) have been show to be id for universe levels lower than the
-- current one n+1.
--
-- concD(absD (D d))
-- = concD (C $ \k p -> k . absTrace . d . concTrace $ p)
-- = D $ \p -> (\k p -> k . absTrace . d . concTrace $ p) (absTrace p) concTrace
-- = D $ \p -> concTrace . absTrace . d . concTrace . absTrace $ p
--   { apply IH, get (concTrace . absTrace = id) for sub-terms }
-- = D $ \p -> id . d . id $ p
-- = D d
--
-- absD(concD c)
-- = absD(concD (C (\k p -> k (f p))))    { parametricity }
-- = absD(D $ \p -> (\k p -> k (f p)) (absTrace p) concTrace)
-- = absD(D $ \p -> concTrace (f (absTrace p)))
-- = C $ \k p -> k . absTrace . (\p -> concTrace (f (absTrace p))) . concTrace $ p
-- = C $ \k p -> k $ absTrace (concTrace (f (absTrace (concTrace p))))
--   { apply IH, get (absTrace . concTrace = id) for sub-terms }
-- = C $ \k p -> k $ id (f (id p))
-- = C $ \k p -> k (f p)
-- = c
absD :: Direct.D -> Cont.C
absD (Direct.D d) = Cont.C $ \k p -> k . absTrace . d . concTrace $ p

concD :: Cont.C -> Direct.D
concD (Cont.C c) = Direct.D $ \p -> concTrace $ c id (absTrace p)

absValue :: Value Direct.D -> Value Cont.C
absValue (Direct.Fun f) = CFun (absD . f . concD)

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

class (AddrOrD d1 ~ d1, AddrOrD d2 ~ d2) => Dimappable d1 d2 where
  dimapValue :: (d1 -> d2) -> (d2 -> d1) -> Value d1 -> Value d2

dimapTrace :: Dimappable d1 d2 => (d1 -> d2) -> (d2 -> d1) -> Trace d1 -> Trace d2
dimapTrace to from (End l) = End l
dimapTrace to from (ConsT l a t) = ConsT l (dimapAction to from a) (dimapTrace to from t)
dimapTrace to from (SnocT t a l) = SnocT (dimapTrace to from t) (dimapAction to from a) l

dimapAction :: Dimappable d1 d2 => (d1 -> d2) -> (d2 -> d1) -> Action d1 -> Action d2
dimapAction to from App1A         = App1A
dimapAction to from (ValA v)      = ValA (dimapValue to from v)
dimapAction to from (App2A n a)   = App2A n (to a)
dimapAction to from (BindA n a d) = BindA n a (to d)
dimapAction to from (LookupA a)   = LookupA a
dimapAction to from (UpdateA a)   = UpdateA a

instance Dimappable Direct.D Cont.C where
  dimapValue to from (Direct.Fun f) = CFun (to . f . from)

instance Dimappable Cont.C Direct.D where
  dimapValue to from (CFun f) = Direct.Fun (to . f . from)

