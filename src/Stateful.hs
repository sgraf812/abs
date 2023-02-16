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
{-# LANGUAGE PatternSynonyms #-}

module Stateful (D(..), DExpr(..), STrace, straceLabels, straceMemory, stateful, statefulD) where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Text.Show (showListWith)

import Expr hiding (Fun)
import qualified ByNeed
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

orElse = flip fromMaybe

data DExpr = Dagger | E LExpr
type Val = LExpr
pattern DVar n <- (E (LVar n))
pattern DApp e x <- (E (LApp e x))
pattern DLam x e <- (E (LLam x e))
pattern DLet x e1 e2 <- (E (LLet x e1 e2))

isVal :: LExpr -> Bool
isVal LLam{} = True
isVal _      = False

type State = (DExpr, Env, Heap, Cont)
type Env = Name :-> Addr
type Heap = Addr :-> (LExpr, Env, D)
type Cont = [Frame]
data Frame
  = Return (Val, Env, SValue)
  | Apply Addr
  | Update Addr
  deriving Show

newtype D = D { unD :: State -> STrace }
data SValue = Fun D deriving Show

type STrace = NonEmpty State

straceLabels :: STrace -> NonEmpty Label
straceLabels = fmap go
  where
    go (Dagger,_,_,_) = daggerLabel
    go (E le,_,_,_)   = le.at

straceMemory :: STrace -> NonEmpty (Env,Heap)
straceMemory = fmap go
  where
    go (_,env,heap,_) = (env,heap)

instance Show DExpr where
  show Dagger = "‡"
  show (E e) = show e.at

srcS, dstS :: STrace -> State
srcS = NE.head
dstS = NE.last


-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> pure p)

instance Eq D where
  _ == _ = True

instance Ord D where
  compare _ _ = EQ

instance Show D where
  show _ = "D"


concatS :: STrace -> STrace -> STrace
concatS (s NE.:| t1) t2 = s NE.:| con s t1 t2
  where
    con :: State -> [State] -> STrace -> [State]
    con s@(e,_,_,_) []      ((e',_,_,_) NE.:| t2) = assert (eqLabel e e') t2
    con _           (s':t1) t2                    = s' : con s' t1 t2

eqLabel :: DExpr -> DExpr -> Bool
eqLabel Dagger Dagger = True
eqLabel (E e1) (E e2) = e1.at == e2.at
eqLabel _      _      = False

-- | Empty list is Nothing (e.g., undefined), non-empty list is Just
type MaybeSTrace = [State]

type PartialD = State -> MaybeSTrace

injD :: D -> PartialD
injD (D d) = \s -> NE.toList (d s)

step :: PartialD -> D
step fun = D $ \s -> s NE.:| fun s

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \s -> let p = d1 s in p `concatS` d2 (dstS p)

stateful :: LExpr -> STrace
stateful le = unD (statefulD le) (E le,Map.empty,Map.empty,[])

statefulD :: LExpr -> D
statefulD le = D $ \s -> case s of
  (E le',_,_,_) | le.at /= le'.at -> unD botD s
  _                               -> unD (go le) s
  where
    go :: LExpr -> D
    go le = case le.thing of
      Var n -> step var1 >.> step var2
      Lam n le' -> step (ret (Fun (go le')))
      App le' n -> step app1 >.> go le' >.> step app2
      Let n le1 le2 -> step (let_ (go le1)) >.> go le2

ret :: SValue -> PartialD
ret v (E sv,env,heap,cont) | isVal sv = [(Dagger, Map.empty, heap, Return (sv, env, v) : cont)]
ret _ _ = []

var1 :: PartialD
var1 (E (LVar x), env, heap, cont)
  | Just a <- Map.lookup x env
  , Just (e, env', d) <- Map.lookup a heap
  = injD d (E e, env', heap, Update a:cont)
var1 _ = []

var2 :: PartialD
var2 (Dagger, env, heap, Return (sv, env', v):Update a:cont)
  | isVal sv
  , Map.null env
  = [(Dagger, env, Map.insert a (sv,env',step d) heap, Return (sv, env', v):cont)]
  where
    d (E sv',_,heap,cont) | sv'.at == sv.at = [(Dagger, Map.empty, heap, Return (sv, env', v):cont)]
    d _ = []
var2 _ = []

app1 :: PartialD
app1 (E (LApp e x), env, heap, cont) | Just a <- Map.lookup x env = [(E e, env, heap, Apply a : cont)]
app1 _ = []

app2 :: PartialD
app2 (Dagger, _, heap, Return (LLam x e, env, Fun d) : Apply a : cont)
  = injD d (E e, Map.insert x a env, heap, cont)
app2 _ = []

let_ :: D -> PartialD
let_ d1 (E (LLet x e1 e2), env,heap,cont)
  | let a = freshAddr heap
  , let env' = Map.insert x a env
  = [(E e2, env', Map.insert a (e1, env', d1) heap, cont)]
let_ _ _ = []

