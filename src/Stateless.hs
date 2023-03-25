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

module Stateless (D(..), Value(Fun), runInit, run, runD,
                  SIAddr, deref', derefInv, step, stepm,
                  materialiseEnv, materialiseEnvForAddr, materialiseHeap') where

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
import qualified Stateful
import qualified Stackless

-- | Finite intialisation trace to infinite or maximal finite trace.
--
-- This type is actually the subtype of `Trace -> Trace` for which every
-- inhabitant `d` satisfies `src(d(p)) = tgt(p)`.
--
-- We can give a partial pointwise prefix order ⊑:
--
-- d1(p) ⊑ d2(p)  <=>  ∃p'. d1(p) `concatT` p' = d2(p)
--
-- Note that a `D` is *not* a monotone map; indeed our semantics isn't.
-- The ordering is to be understood pointwise, ⊑^. .
--
-- There exists a bottom element `⊥(p) = End (tgt p)` and directed sets have a
-- the pointwise supremum ⊔^.
-- (Finite case is simply the max element; infinite case is the limit of the
-- prefix traces).
-- Thus, (D,⊑^.,⊥,⊔^.) forms a CPO with bottom element ⊥.
-- Note that ⊥ represents an expression that is stuck in every context;
-- values do at least another step in our semantics.
--
newtype D = D { unD :: Trace D -> Trace D }
instance Eq D where _ == _ = True
instance Show D where show _ = "D"

newtype Value = Fun ((SIAddr, D) -> D)
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "(fun)"

--
-- * Action instantiation
--

type instance StateX D = ProgPoint D
type instance RetX D = NoInfo
type instance ValX D = Value

-- | Note that the SIAddr is irrelevant to the semantics; think of it as "there
-- exists Addr `a` such that D is `deref a`
type instance EnvRng D = (SIAddr, D)

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End (tgt p))

concatD :: HasCallStack => D -> D -> D
concatD (D d1) (D d2) = D $ \p -> let p1 = d1 p in p1 `concatT` (d2 (p `concatT` p1))
infixr 5 `concatD`

(>.>) :: HasCallStack => D -> D -> D
(>.>) = concatD
infixr 5 >.>

askP :: (Trace D -> D) -> D
askP f = D $ \p -> unD (f p) p

whenP :: Maybe a -> (a -> D) -> D
whenP Nothing  _ = botD
whenP (Just a) d = d a

whenAtP :: ProgPoint D -> D -> D
whenAtP l d = askP $ \p -> if labelOf l == labelOf (tgt p) then d else botD

step :: Action D -> ProgPoint D -> D
step a l = D $ \p -> ConsT (tgt p) a (End l)

stepm :: ProgPoint D -> Action D -> ProgPoint D -> D
stepm l1 a l2 = whenAtP l1 (step a l2)

deref :: HasCallStack => Addr -> D
deref a = askP $ \pi -> case materialiseHeap pi a of
  Just (le, d) -> step (LookupA (LI a)) (E le) >.> d >.> stepm (Ret NI) (UpdateA (UI a)) (Ret NI)
  Nothing      -> error ("out of scope, caught too late " ++ show a ++ " " ++ show pi)

-- | Corresponds to the dependent sum (∃a.deref a),
-- allowing us to extract both the d = deref a and the a from whence it came
deref' :: Addr -> (SIAddr, D)
deref' = mkInvertible deref

derefInv :: (SIAddr, D) -> Addr
derefInv (SI a, _d) = a -- such that deref a = _d

materialiseHeap :: Trace D -> Addr -> Maybe (LExpr, D)
materialiseHeap pi addr = update_or_bind pi
  where
    update_or_bind pi'@ConsT{} = update_or_bind (snocifyT pi')
    update_or_bind (SnocT pi' a _)
      | UpdateA ui <- a :: Action D
      , addr == ui.addr
      , Just (p@(E le), v) <- valT pi'
      = Just (le, stepm p (ValA v) (Ret NI))
      | BindA bi <- a
      , addr == bi.addr
      = Just (bi.rhs, bi.denot)
      | otherwise
      = update_or_bind pi'
    update_or_bind End{} = Nothing

runD :: LExpr -> Env (SIAddr, D) -> D
runD le env = go le env
  where
    (!⊥) :: Ord a => (a :-> (SIAddr, D)) -> a -> D
    env !⊥ x = snd <$> env Map.!? x `orElse` botD
    go :: LExpr -> Env (SIAddr, D) -> D
    go le !env = whenAtP (E le) $ case le.thing of
      Var n -> env !⊥ n
      App le n -> whenP (Map.lookup n env) $ \d ->
        let apply = askP $ \p -> whenP (val p) $ \(Fun f) -> f d
         in step (App1A (A1I d)) (E le) >.> go le env >.> apply
      Lam n le' ->
        let val = Fun (\d -> step (App2A (A2I n d)) (E le') >.> go le' (Map.insert n d env))
         in step (ValA val) (Ret NI)
      Let n le1 le2 -> askP $ \p ->
        let a = hash p
            env' = Map.insert n (deref' a) env
         in step (BindA (BI n le1 a (go le1 env'))) (E le2) >.> go le2 env'
    blah (ConsT _ a _) = a

run :: LExpr -> Env (SIAddr, D) -> Trace D -> Trace D
run le env p = unD (runD le env) p

runInit :: LExpr -> Trace D
runInit le = run le Map.empty (End (E le))

-- | A version of `materialiseHeap` that returns a finite map instead of a
-- Maybe valued function. In doing so, we can collect all points in a single
-- trace traversal and get to query the domain of the heap
materialiseHeap' :: Trace D -> Addr :-> (LExpr, D)
materialiseHeap' pi = go pi
  where
    go pi'@ConsT{} = go (snocifyT pi')
    go (SnocT pi' a _) = case a of
      UpdateA ui | Just (p@(E le), v) <- valT pi'
        -> Map.insert ui.addr (le, stepm p (ValA v) (Ret NI)) (go pi')
      BindA bi
        -> Map.insert bi.addr (bi.rhs, bi.denot) (go pi')
      _ -> go pi'
    go End{} = Map.empty

-- | μ_ρ, the (missing) middle component of the stateful heap, calculating the
-- environment for a heap entry
materialiseEnvForAddr :: HasCallStack => Trace D -> Addr -> Env (SIAddr, D)
materialiseEnvForAddr p a = go (snocifyT p)
  where
    go p@ConsT{} = go (snocifyT p)
    go   (End l) = Map.empty
    go   (SnocT p' (UpdateA ui) _) | ui.addr == a = materialiseEnv p'
    go p@(SnocT _  (BindA bi)   _) | bi.addr == a = materialiseEnv p
    go   (SnocT p  _            _)                = go p

-- | varrho, calculating the environment at the end of an initialisation trace
materialiseEnv :: Trace D -> Env (SIAddr, D)
materialiseEnv p = go p
  where
    go p@ConsT{} = go (snocifyT p)
    go (End l) = Map.empty
    go (SnocT p a _) = case a of
      BindA bi   -> Map.insert bi.name (deref' bi.addr) (go p)
      App2A ai   -> Map.insert ai.name ai.arg (go p)
      LookupA li -> materialiseEnvForAddr p li.addr
      _          -> go p
