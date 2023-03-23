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
                  SIAddr, wrapLookup, step) where

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
instance Eq D where _ == _ = True
instance Show D where show _ = "D"

newtype Value = Fun ((SIAddr, D) -> D)
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "fun"

--
-- * Action instantiation
--

type instance StateX D = ProgPoint D
type instance RetX D = NoInfo
type instance ValX D = Value

-- | Note that the SIAddr is irrelevant to the semantics; think of it as "there
-- exists Addr `a` such that D is `memo a`
type instance EnvRng D = (SIAddr, D)

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End (dst p))

concatD :: HasCallStack => D -> D -> D
concatD (D d1) (D d2) = D $ \p -> let p1 = d1 p in p1 `concatT` d2 (p `concatT` p1)
infixr 5 `concatD`

(>.>) :: HasCallStack => D -> D -> D
(>.>) = concatD

askP :: (Trace D -> D) -> D
askP f = D $ \p -> unD (f p) p

whenP :: Maybe a -> (a -> D) -> D
whenP Nothing  _ = botD
whenP (Just a) d = d a

whenAtP :: ProgPoint D -> D -> D
whenAtP l d = askP $ \p -> if labelOf l == labelOf (dst p) then d else botD

step :: Action D -> ProgPoint D -> D
step a l = D $ \p -> ConsT (dst p) a (End l)

stepm :: ProgPoint D -> Action D -> ProgPoint D -> D
stepm l1 a l2 = whenAtP l1 (step a l2)

memo :: Addr -> D
memo a = askP $ \pi ->
  let pi' = snocifyT pi
      (p', d) =   update a pi'
              <|> bind a pi'
              `orElse` error ("out of scope, caught too late " ++ show a)

      update addr (SnocT pi' a _)
        | UpdateA ui <- a :: Action D
        , addr == ui.addr
        = (\(p, v) -> (p, stepm p (ValA v) (Ret NI))) <$> valT pi'
        | otherwise
        = update addr pi'
      update _ End{} = Nothing

      bind addr (SnocT pi' a _)
        | BindA bi <- a
        , addr == bi.addr
        = Just (E bi.rhs, bi.denot)
        | otherwise
        = bind addr pi'
      bind _ End{} = Nothing

  in wrapLookup a p' d

wrapLookup :: Addr -> ProgPoint D -> D -> D
wrapLookup a p d =
  step (LookupA (LI a)) p >.> d >.> stepm (Ret NI) (UpdateA (UI a)) (Ret NI)

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
            env' = Map.insert n (SI a, memo a) env
         in step (BindA (BI n le1 a (go le1 env'))) (E le2) >.> go le2 env'

run :: LExpr -> Env (SIAddr, D) -> Trace D -> Trace D
run le env p = unD (runD le env) p

runInit :: LExpr -> Trace D
runInit le = run le Map.empty (End (E le))
