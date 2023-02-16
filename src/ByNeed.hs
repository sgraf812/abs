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
               D(..), Lifted(..), denot) where

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
        (App e x, _) | Map.member x h -> go (h, e, Apply x : s)
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
        BindA{}      | Let n e1 e2 <- e ->
          let n' = freshName n h
              e1' = subst n n' e1
              e2' = subst n n' e2
              c1 = (Map.insert n' e1' h, e2', s)
           in yield p c1
        App1A        | App e n <- e ->
          let c1 = (h, e, Apply n:s)
              (p1,~(Just (ConsT l App2A{} p2))) = splitBalancedPrefix p
              cs1 = yield p1 c1
              (h',Fix (Lam m eb),Apply n':s') = last cs1
              c2 = (h', subst m n' eb, s')
              cs2 = yield p2 c2
           in -- trace ("app1: " ++ unlines [show c1,show p, show p1, show p2]) $
              cs1 ++ cs2

        LookupA _    | Var n <- e ->
          let c1 = (h, h Map.! n, Update n:s)
              (p1,mb_p2) = splitBalancedPrefix p
              cs1 = yield p1 c1
              (h',e',Update n':s') = last cs1
              c2 = (Map.insert n' e' h', e', s')
              cs2 = case mb_p2 of
                Just (ConsT l UpdateA{} p2) -> yield p2 c2
                _                           -> []
           in -- trace ("look: " ++ show c1 ++ show (takeT 4 p1)) $
              cs1 ++ cs2

        _ -> -- trace (show l ++ " " ++ show a ++ " " ++ show (Fix e) ++ "\n"  ++ show (takeT 20 p0) ++ "\n" ++ show (takeT 20 p))
             []

defnSmallStep :: Show d => Expr -> (Trace d -> Trace d) -> [Configuration]
defnSmallStep e sem = config e (sem (End ((label e).at)))

data SSValue = SVBot | SVFun (SS -> SS)

type SS = (SSValue, Configuration -> SmallTrace)

botSS :: SS
botSS = (SVBot, EndS)

absSmallStepEntry :: LExpr -> [Configuration]
absSmallStepEntry le = extractConfigurations $ snd (absSmallStep (unlabel le) Map.empty) init
  where
    init = (Map.empty, unlabel le, [])

data Transition = LookupT | UpdateT | App1T | App2T | LetT deriving (Show, Eq, Ord)

okTransition :: Transition -> Configuration -> Maybe Configuration
okTransition LookupT (h,FVar x,s) | Just e <- Map.lookup x h = Just (h, e, Update x : s)
okTransition UpdateT (h,v@FLam{},Update x : s) = Just (Map.insert x v h, v, s)
okTransition App1T   (h,FApp e x,s) | Map.member x h = Just (h, e, Apply x : s)
okTransition App2T   (h,FLam x e,Apply y : s) = Just (h, subst x y e, s)
okTransition LetT    (h,FLet x e1 e2,s) = Just (Map.insert x' e1' h, e2', s)
  where
    x' = freshName x h
    e1' = subst x x' e1
    e2' = subst x x' e2
--okTransition t c | trace (show t ++ " " ++ show c) True = undefined
okTransition _ _ = Nothing

data SmallTrace
  = EndS !Configuration
  | ConsS !Configuration !Transition SmallTrace
  | SnocS SmallTrace !Transition !Configuration

extractConfigurations :: SmallTrace -> [Configuration]
extractConfigurations s = go (consifyS s)
  where
    go (EndS c) = [c]
    go (ConsS c t s) = assert (isJust (okTransition t c)) $
                       c : go s

srcS, dstS :: SmallTrace -> Configuration
srcS (EndS c) = c
srcS (ConsS c _ _) = c
srcS (SnocS s _ _) = srcS s
dstS (EndS c) = c
dstS (SnocS _ _ c) = c
dstS (ConsS _ _ s) = dstS s

consifyS :: SmallTrace -> SmallTrace
consifyS s = go EndS s
  where
    go f (EndS c) = f c
    go f (ConsS c t s) = ConsS c t (go f s)
    go f (SnocS s t c) = go (\c' -> ConsS c' t (f c)) s

snocifyS :: SmallTrace -> SmallTrace
snocifyS s = go EndS s
  where
    go f (EndS c) = f c
    go f (SnocS s t c) = SnocS (go f s) t c
    go f (ConsS c t s) = go (\c' -> SnocS (f c) t c') s

concatS :: SmallTrace -> SmallTrace -> SmallTrace
concatS s1 s2 = con s1 s2
  where
    con :: SmallTrace -> SmallTrace -> SmallTrace
    con (EndS c) s2 = assert (c == srcS s2) s2
    con (SnocS s1 t c) s2 = con s1 (assert (c == srcS s2) (ConsS (dstS s1) t s2))
    con (ConsS c t s1) s2 = ConsS c t (con s1 s2)

cons :: Transition -> (Configuration -> SmallTrace) -> (Configuration -> SmallTrace)
cons t f c1 = case okTransition t c1 of
  Just c2 -> ConsS c1 t (f c2)
  Nothing -> EndS c1

snoc :: (Configuration -> SmallTrace) -> Transition -> (Configuration -> SmallTrace)
snoc f t c | let s = f c = s `concatS` case okTransition t (dstS s) of
  Just c2 -> SnocS (EndS (dstS s)) t c2
  Nothing -> (EndS (dstS s))

shortcut :: (Configuration -> SmallTrace) -> (Configuration -> SmallTrace)
shortcut _ c@(_,v@FLam{},Update x:_) = EndS c
shortcut f c                         = f c

funnyForwardCompose :: (Configuration -> SmallTrace) -> (Configuration -> SmallTrace) -> (Configuration -> SmallTrace)
funnyForwardCompose f g c = let s = f c in s `concatS` g (dstS s)

absSmallStep :: Expr -> (Name :-> SS) -> SS
absSmallStep (Fix e) env = case e of
  Var x   -> Map.findWithDefault botSS x env
  Lam x e -> (SVFun (\d -> absSmallStep e (Map.insert x d env)), EndS)
  App e x ->
    let (v1, trans1) = absSmallStep e env
        (v2, trans2) = case v1 of
          SVFun f -> f (Map.findWithDefault botSS x env)
          _       -> botSS
     in (v2, funnyForwardCompose (cons App1T trans1) (cons App2T trans2))
  Let x e1 e2 ->
    let (v1, trans1) = absSmallStep e1 env'
        (v2, trans2) = absSmallStep e2 env'
        env' = Map.insert x d env
        d = (v1,snoc(cons LookupT (shortcut trans1)) UpdateT)
     in (v2, cons LetT trans2)

-- | convenience
runSS :: Int -> String -> IO ()
runSS n s = mapM_ print $ take n $ absSmallStepEntry (label (uniqify (read s)))

data D = DBot' | DFun' (D -> D)

denot :: Expr -> (Name :-> D) -> D
denot (Fix e) env = case e of
  Var n   -> env !⊥ n
  Lam n e -> DFun' (\d -> denot e (Map.insert n d env))
  App e n -> case denot e env of
    DFun' f -> f (env !⊥ n)
    _      -> DBot'
  Let n e1 e2 ->
    let env' = Map.insert n (denot e1 env') env in
    denot e2 env'
  where
    (!⊥) :: Ord a => (a :-> D) -> a -> D
    env !⊥ x = Map.findWithDefault DBot' x env

-- post(go le []) will be the reachability semantics, e.g., small-step!
-- Wart: Instead of a (set of) Trace `t`, it should take a (set of) Configuration `c`
-- such that `config p = c` (that is, we don't know how to efficiently compute
-- the concretisation function γ(cs) = ts). By doing it this way, we can
-- actually compute.
-- The lifting to sets (of initialisation Traces/Configurations) is routine.
-- we return a list instead of a set, because it might be infinite and we want to
-- enumerate.
post :: Show d => (LExpr -> Trace d -> Trace d) -> LExpr -> Trace d -> Label -> [[ByNeed.Configuration]]
post sem e p l = map (config (unlabel e)) (pointwise sem e p l)

