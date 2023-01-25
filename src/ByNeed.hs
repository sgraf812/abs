{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}

module ByNeed (Configuration, Heap, Stack, Frame(..),
               smallStep, config, defnSmallStep, absSmallStep,
               absSmallStepEntry,
               D(.., DFun, DBot), Lifted(..), denot) where

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
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty

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
config e p0 = yield (consifyT p0) init
  where
    init = (Map.empty, e, [])
    traceIt f res = trace (f res) res
    yield t c = c : go t c
    go (End l) _ = []
    go (ConsT l a p) c0@(h, Fix e, s) = -- trace ("her " ++ unlines [show c0, show a, show p]) $
      case a of
        ValA _ -> go p c0 -- No corresponding small-step transition
        BindA        | Let n e1 e2 <- e ->
          let n' = freshName n h
              e1' = subst n n' e1
              e2' = subst n n' e2
              c1 = (Map.insert n' e1' h, e2', s)
           in yield p c1
        App1A        | App e n <- e ->
          let c1 = (h, e, Apply n:s)
              (p1,~(Just (ConsT l App2A p2))) = splitBalancedPrefix p
              cs1 = yield p1 c1
              (h',Fix (Lam m eb),Apply n':s') = last cs1
              c2 = (h', subst m n' eb, s')
              cs2 = yield p2 c2
           in -- trace ("app1: " ++ unlines [show c1,show p, show p1, show p2]) $
              cs1 ++ cs2

        LookupA _    | Var n <- e ->
          let c1 = (h, h Map.! n, Update n:s)
              (p1,~(Just p2)) = splitBalancedPrefix p
              cs1 = yield p1 c1
              (h',e',Update n':s') = last cs1
              c2 = (Map.insert n' e' h', e', s')
              cs2 = yield p2 c2
           in -- trace ("look: " ++ show c1 ++ show (takeT 4 p1)) $
              cs1 ++ cs2

        _ -> error (show l ++ " " ++ show a ++ " " ++ show (Fix e) ++ "\n"  ++ show (takeT 20 p0) ++ "\n" ++ show (takeT 20 p))

defnSmallStep :: Show d => Expr -> (Trace d -> Trace d) -> [Configuration]
defnSmallStep e sem = config e (sem (End ((label e).at)))

newtype SSValue = SV (Lifted (Value SS))

pattern SVFun :: (SS -> SS) -> SSValue
pattern SVFun f = SV (Lifted (Fun f))

pattern SVBot :: SSValue
pattern SVBot = SV Bottom

type SS = (SSValue, Configuration -> [Configuration])

botSS :: SS
botSS = (SV Bottom, const [])

absSmallStepEntry :: LExpr -> [Configuration]
absSmallStepEntry le = init : snd (absSmallStep (unlabel le) Map.empty) init
  where
    init = (Map.empty, unlabel le, [])

absSmallStep :: Expr -> (Name :-> SS) -> SS
absSmallStep (Fix e) env = case e of
  Var x   -> Map.findWithDefault botSS x env
  Lam x e -> (SVFun (\d -> absSmallStep e (Map.insert x d env)), \(_,FLam _ _,_) -> [])
  App e x ->
    let (v,  trans1) = absSmallStep e env
        (v', trans2) = case v of
          SVFun f -> f (Map.findWithDefault botSS x env)
          _       -> botSS
        trans (h1,FApp e1 x1, s1) =
          let c1 = (h1, e1, Apply x1:s1)
              cs1 = c1 : trans1 c1
              cs2 = case last cs1 of
                (h2,FLam x2 e2, Apply y2:s2)
                  | let !(SVFun _) = v
                  , let c2 = (h2, subst x2 y2 e2, s2)
                  -> c2 : trans2 c2
                _ -> []
           in cs1 ++ cs2
     in (v', trans)
  Let x e1 e2 ->
    let env' = Map.insert x d env
        (v1, trans1) = absSmallStep e1 env'
        (v2, trans2) = absSmallStep e2 env'
        d = (v1,trans_memo trans1)
        lookup _     (h', v'@FLam{},Update x':s') = [(Map.insert x' v' h', v', s')]
        lookup trans c                            = trans c
        trans_memo trans (h',FVar x',s') =
          let e1' = h' Map.! x'
              c1 = (h',e1',Update x':s')
              cs = trans1 c1
          in c1 : case e1' of
            FLam{} -> [(Map.insert x' e1' h', e1', s')] -- perhaps test here whether e1 was *not* a value. But it doesn't matter much
            _      -> cs ++ case last cs of
              (h', v1', Update x':s') -> [(Map.insert x' v1' h', v1', s')]
              _                       -> []
        trans_let (h',FLet x' e1' e2', s') =
          let x'' = freshName x' h'
              e1'' = subst x' x'' e1'
              e2'' = subst x' x'' e2'
              c' = (Map.insert x'' e1'' h', e2'', s')
           in c' : trans2 c'
     in (v2, trans_let)

newtype D = D (Lifted (Value D))

pattern DFun :: (D -> D) -> D
pattern DFun f = D (Lifted (Fun f))

pattern DBot :: D
pattern DBot = D Bottom

denot :: Expr -> (Name :-> D) -> D
denot (Fix e) env = case e of
  Var n   -> env !⊥ n
  Lam n e -> DFun (\d -> denot e (Map.insert n d env))
  App e n -> case denot e env of
    DFun f -> f (env !⊥ n)
    _      -> DBot
  Let n e1 e2 ->
    let env' = Map.insert n (denot e1 env') env in
    denot e2 env'
  where
    (!⊥) :: Ord a => (a :-> D) -> a -> D
    env !⊥ x = Map.findWithDefault DBot x env

