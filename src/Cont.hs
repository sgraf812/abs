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
{-# LANGUAGE TupleSections #-}

module Cont (C(..), run, absD, concD, absTrace, concTrace) where

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
import qualified Stateless

import Expr
import Data.Bifunctor (second)

newtype C = C { unC :: (Trace C -> Trace C) -> Trace C -> Trace C }
instance Eq C where _ == _ = True
instance Show C where show _ = "C"

newtype Value = Fun ((SIAddr,C) -> C)
instance Eq Value where _ == _ = True
instance Show Value where show _ = "fun"

type instance StateX C = ProgPoint C
type instance RetX C = NoInfo
type instance ValX C = Value
type instance EnvRng C = (SIAddr, C)

botC :: C
botC = C $ \k p -> k (End (tgt p))

step :: Action C -> ProgPoint C -> C
step a l = C $ \k p -> ConsT (tgt p) a $ k $ SnocT p a l

stepRet :: Action C -> C
stepRet a = C $ \k p ->
  if labelOf (tgt p) /= returnLabel
    then k p
    else ConsT (tgt p) a $ k $ SnocT p a (tgt p)

whenAtP :: Label -> C -> C
whenAtP l c = askP $ \p -> if l == labelOf (tgt p) then c else botC

memo :: Addr -> ProgPoint C -> C -> C
memo a l sem = askP $ \pi ->
  let (l', d) = case update a (snocifyT pi) of
        Just (l', v) -> (l', step (ValA v) (Ret NI))
        Nothing      -> (l, sem)
      update addr (SnocT pi' a _)
        | UpdateA ai <- a
        , addr == ai.addr
        = valT pi'
        | otherwise  = update addr pi'
      update _ End{} = Nothing
  in step (LookupA (LI a)) l' <++> d <++> whenAtP returnLabel (step (UpdateA (UI a)) (Ret NI))

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

(>->) :: Action C -> ProgPoint C -> C
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

(!⊥) :: Env (a, C) -> Name -> C
env !⊥ x = snd <$> env Map.!? x `orElse` botC

run :: LExpr -> (Env (SIAddr, C)) -> Trace C -> Trace C
run le env p
  | labelOf (tgt p) /= le.at = unC botC id p
  | otherwise                = unC (go le env) (End . tgt) p
  where
    go :: LExpr -> (Env (SIAddr, C)) -> C
    go le !env = case le.thing of
      Var n -> env !⊥ n
      App le n ->
        case Map.lookup n env of
          Just d ->
            let apply = askP $ \p -> case val p of
                  Just (Fun f) -> f d
                  Nothing      -> botC
             in step (App1A (A1I d)) (E le) <++> go le env <++> apply
          Nothing -> botC
      Lam n le' ->
        let val = Fun (\c -> App2A (A2I n c) >-> E le' <++> go le' (Map.insert n c env))
         in step (ValA val) (Ret NI)
      Let n le1 le2 -> askP $ \p ->
        let a = alloc p
            c = memo a (E le1) (go le1 env')
            env' = Map.insert n (SI a,c) env
         in step (BindA (BI n le1 a c)) (E le2) <++> go le2 env'

-- | As Reynolds first proved in "On the relation between Stateless and
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
absD :: Stateless.D -> Cont.C
absD (Stateless.D d) = Cont.C $ \k p -> k . absTrace . d . concTrace $ p

concD :: Cont.C -> Stateless.D
concD (Cont.C c) = Stateless.D $ \p -> concTrace $ c id (absTrace p)

absValue :: Stateless.Value -> Value
absValue (Stateless.Fun f) = Fun (absD . f . second concD)

absAction :: Action Stateless.D -> Action Cont.C
absAction = dimapAction absD concD

concAction :: Action Cont.C -> Action Stateless.D
concAction = dimapAction concD absD

-- | (Inductive) Assumption: (absD . concD = id), (concD . absD = id)
--
--   absTrace (concTrace p)
-- = dimapTrace absD concD (dimapTrace concD absD p)
-- = dimapTrace (absD . concD) (concD . absD) p
-- = dimapTrace id id p
-- = p
absTrace :: Trace Stateless.D -> Trace Cont.C
absTrace = dimapTrace absD concD

concTrace :: Trace Cont.C -> Trace Stateless.D
concTrace = dimapTrace concD absD

class (EnvRng d1 ~ (SIAddr, d1), EnvRng d2 ~ (SIAddr, d2)) => Dimappable d1 d2 where
  dimapValue :: (d1 -> d2) -> (d2 -> d1) -> ValX d1 -> ValX d2
  dimapState :: (d1 -> d2) -> (d2 -> d1) -> StateX d1 -> StateX d2

dimapTrace :: Dimappable d1 d2 => (d1 -> d2) -> (d2 -> d1) -> Trace d1 -> Trace d2
dimapTrace to from (End l) = End (dimapState to from l)
dimapTrace to from (ConsT l a t) = ConsT (dimapState to from l) (dimapAction to from a) (dimapTrace to from t)
dimapTrace to from (SnocT t a l) = SnocT (dimapTrace to from t) (dimapAction to from a) (dimapState to from l)

dimapAction :: Dimappable d1 d2 => (d1 -> d2) -> (d2 -> d1) -> Action d1 -> Action d2
dimapAction to from (App1A ai)   = App1A (A1I (second to ai.arg1))
dimapAction to from (ValA v)    = ValA (dimapValue to from v)
dimapAction to from (App2A ai)  = App2A (A2I ai.name (second to ai.arg))
dimapAction to from (BindA bi)  = BindA (bi { denot = to bi.denot })
dimapAction to from (LookupA a) = LookupA a
dimapAction to from (UpdateA a) = UpdateA a

instance Dimappable Stateless.D Cont.C where
  dimapValue to from (Stateless.Fun f) = Fun (to . f . second from)
  dimapState _  _                      = mapProgPoint id

instance Dimappable Cont.C Stateless.D where
  dimapValue to from (Fun f) = Stateless.Fun (to . f . second from)
  dimapState _  _            = mapProgPoint id

