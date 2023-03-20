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

module Stateful (D(..), ProgPoint(..), Trace, traceLabels, traceMemory, run, runD) where

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

import Expr hiding (Fun, Trace, traceLabels)
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

orElse = flip fromMaybe

type State = (ProgPoint (Val, SValue), Env, Heap, Cont)
type Env = Name :-> Addr
type Heap = Addr :-> (LExpr, Env, D)
type Cont = [Frame]
data Frame
  = Apply Addr
  | Update Addr
  deriving Show

newtype D = D { unD :: State -> Trace }
data SValue = Fun D deriving Show

type Trace = NonEmpty State

traceLabels :: Trace -> NonEmpty Label
traceLabels = fmap go
  where
    go (Ret _,_,_,_) = returnLabel
    go (E le,_,_,_)  = le.at

traceMemory :: Trace -> NonEmpty (Env,Heap)
traceMemory = fmap go
  where
    go (_,env,heap,_) = (env,heap)

srcS, dstS :: Trace -> State
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


concatS :: Trace -> Trace -> Trace
concatS (s NE.:| t1) t2 = s NE.:| con s t1 t2
  where
    con :: State -> [State] -> Trace -> [State]
    con s@(e,_,_,_) []      ((e',_,_,_) NE.:| t2) = assert (eqPoint e e') t2
    con _           (s':t1) t2                    = s' : con s' t1 t2

-- | Empty list is Nothing (e.g., undefined), non-empty list is Just
type MaybeSTrace = [State]

type PartialD = State -> MaybeSTrace

injD :: D -> PartialD
injD (D d) = \s -> NE.toList (d s)

step :: PartialD -> D
step fun = D $ \s -> s NE.:| fun s

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \s -> let p = d1 s in p `concatS` d2 (dstS p)

run :: LExpr -> Trace
run le = unD (runD le) (E le,Map.empty,Map.empty,[])

runD :: LExpr -> D
runD le = D $ \s -> case s of
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
ret v (E sv,env,heap,cont) | isVal sv = [(Ret (sv,v), env, heap, cont)]
ret _ _ = []

var1 :: PartialD
var1 (E (LVar x), env, heap, cont)
  | Just a <- Map.lookup x env
  , Just (e, env', d) <- Map.lookup a heap
  = injD d (E e, env', heap, Update a:cont)
var1 _ = []

var2 :: PartialD
var2 (Ret (sv, v), env, heap, Update a:cont)
  | isVal sv
  = [(Ret (sv,v), env, Map.insert a (sv,env,step d) heap, cont)]
  where
    d (E sv',env,heap,cont) | sv'.at == sv.at = [(Ret (sv,v), env, heap, cont)]
    d _ = []
var2 _ = []

app1 :: PartialD
app1 (E (LApp e x), env, heap, cont) | Just a <- Map.lookup x env = [(E e, env, heap, Apply a : cont)]
app1 _ = []

app2 :: PartialD
app2 (Ret (LLam x e, Fun d), env, heap, Apply a : cont)
  = injD d (E e, Map.insert x a env, heap, cont)
app2 _ = []

let_ :: D -> PartialD
let_ d1 (E (LLet x e1 e2), env,heap,cont)
  | let a = freshAddr heap
  , let env' = Map.insert x a env
  = [(E e2, env', Map.insert a (e1, env', d1) heap, cont)]
let_ _ _ = []

