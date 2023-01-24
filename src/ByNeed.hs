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

module ByNeed (Configuration, Heap, Stack, Frame(..), smallStep, config, defnSmallStep, D(..), denot) where

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

orElse = flip fromMaybe

type Configuration = (Heap, Expr, Stack)
type Heap = Name :-> Expr
type Stack = [Frame]
data Frame
  = Apply Name
  | Update Name
  deriving Eq

instance {-# OVERLAPPING #-} Show Heap where
  showsPrec _ h = showListWith (\(x, e) -> ((x ++ "↦" ++ show e) ++)) $ Map.assocs h

instance Show Frame where
  show (Apply x) = "$" ++ x
  show (Update x) = "#" ++ x

smallStep :: Expr -> [Configuration]
smallStep e = go (Map.empty, e, [])
  where
    go :: Configuration -> [Configuration]
    go c@(h, fe@(Fix e), s) =
      c : case (e, s) of
        (Var n, _) | n `Map.member` h -> go (h, h Map.! n, Update n:s)
        (App e x, _) -> go (h, e, Apply x : s)
        (Lam x e, []) -> []
        (Lam x e, Apply y : s') -> go (h, subst x y e, s')
        (Let x e1 e2, _) ->
          let x' = freshName x h
           in go (Map.insert x' (subst x x' e1) h, (subst x x' e2), s)
        (Lam{}, Update y:s) -> go (Map.insert y fe h, fe, s)
        _ -> [] -- stuck

-- | Reconstruct a Configuration sequence from a trace of the program
-- The abstraction function to machine configurations.
config :: Show d => Expr -> Trace d -> [Configuration]
config e p0 = init : go (consifyT p0) init
  where
    init = (Map.empty, e, [])
    traceIt f res = trace (f res) res
    go :: Show d => Trace d -> Configuration -> [Configuration]
    go (End l) _ = []
    go (ConsT l a p) c0@(h, Fix e, s) = -- trace ("her " ++ unlines [show c0, show a, show p]) $
      case a of
        ValA _ -> go p c0 -- No corresponding small-step transition
        BindA        | Let n e1 e2 <- e ->
          let n' = freshName n h
              e1' = subst n n' e1
              e2' = subst n n' e2
              c1 = (Map.insert n' e1' h, e2', s)
           in c1 : go p c1
        App1A        | App e n <- e ->
          let c1 = (h, e, Apply n:s)
              (p1,~(Just (ConsT l App2A p2))) = splitBalancedPrefix p
              cs2 = c1 : go p1 c1
              (h',Fix (Lam m eb),Apply n':s') = last cs2
              c2 = (h', subst m n' eb, s')
           in -- trace ("app1: " ++ unlines [show c1,show p, show p1, show p2]) $
              cs2 ++ c2 : go p2 c2

        LookupA _    | Var n <- e ->
          let c1 = (h, h Map.! n, Update n:s)
              (p1,~(Just p2)) = splitBalancedPrefix p
              cs2 = c1 : go p1 c1
              (h',e',Update n':s') = last cs2
              c2 = (Map.insert n' e' h', e', s')
           in -- trace ("look: " ++ show c1) $
              cs2 ++ c2 : go p2 c2

        _ -> error (show a ++ " " ++ show (Fix e) ++ " " ++ show (takeT 20 p0) ++ show (takeT 20 p))

defnSmallStep :: Show d => Expr -> (Trace d -> Trace d) -> [Configuration]
defnSmallStep e sem = config e (sem (End ((label e).at)))

data D = V (Value D)
       | Bottom
       deriving Show

(!⊥) :: Ord a => (a :-> D) -> a -> D
env !⊥ x = Map.findWithDefault Bottom x env

denot :: Expr -> (Name :-> D) -> D
denot (Fix e) env = case e of
  Var n   -> env Map.!? n `orElse` Bottom
  Lam n e -> V (Fun (\d -> denot e (Map.insert n d env)))
  App e n -> case denot e env of
    V (Fun f) -> f (env !⊥ n)
    _         -> Bottom
  Let n e1 e2 ->
    let env' = Map.insert n (denot e1 env') env in
    denot e2 env'

