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

module ByName (Configuration, Heap, Stack, Frame(..), smallStep, config, defnSmallStep) where

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

type Configuration = (Heap, Expr, Stack)
type Heap = Name :-> Expr
type Stack = [Frame]
data Frame = Apply Name

instance Show Frame where
  show (Apply x) = "$" ++ x

instance {-# OVERLAPPING #-} Show Heap where
  showsPrec _ h = showListWith (\(x, e) -> ((x ++ "↦" ++ show e) ++)) $ Map.assocs h

smallStep :: Expr -> [Configuration]
smallStep e = go (Map.empty, e, [])
  where
    go :: Configuration -> [Configuration]
    go c@(h, Fix e, s) =
      c : case (e, s) of
        (Var n, _) | n `Map.member` h -> go (h, h Map.! n, s)
        (App e x, _) -> go (h, e, Apply x : s)
        (Lam x e, []) -> []
        (Lam x e, Apply y : s') -> go (h, subst x y e, s')
        (Let x e1 e2, _) ->
          let x' = freshName x h
           in go (Map.insert x' (subst x x' e1) h, (subst x x' e2), s)
        _ -> [] -- stuck

-- | Reconstruct a Configuration from a trace of the program
config :: Expr -> Trace d -> Configuration
config e p = go (snocifyT p)
  where
    go :: Trace d -> Configuration
    go ConsT {} = undefined
    go (End l) = (Map.empty, e, [])
    go (SnocT t a l) =
      let c@(h,Fix e,s) = go t in
      case a of
        BindA _ _ _  | Let n e1 e2 <- e ->
          let n' = freshName n h
              e1' = subst n n' e1
              e2' = subst n n' e2
           in (Map.insert n' e1' h, e2', s)
        AppA _       | App e n <- e -> (h, e, Apply n:s)
        ValA (Fun _) | Lam _ _ <- e -> c -- No corresponding small-step transition
        BetaA _      | (Apply n':s') <- s, Lam n eb <- e -> (h, subst n n' eb, s')
        EnterA      | Var n <- e -> (h, h Map.! n, s)
        _ -> undefined

defnSmallStep :: Show d => Expr -> (Trace d -> Trace d) -> [Configuration]
defnSmallStep e sem = map (config e) $ filter (not . lastIsVal) $ (prefs (sem (End (le.at))))
  where
    le = label e
    -- Value transitions have no corresponding small-step transition, hence we exclude them
    lastIsVal t = case snocifyT t of
      SnocT _ ValA{} _ -> True
      _                -> False
