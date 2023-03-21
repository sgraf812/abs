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
{-# LANGUAGE TypeFamilies #-}

module Stateful (D(..), ProgPoint(..), Trace, traceMemory, run, runD) where

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

import Expr
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

orElse = flip fromMaybe

type Env = Name :-> Addr
type Heap = Addr :-> (LExpr, Env, D)
type Cont = [Frame]
data Frame
  = Apply Addr
  | Update Addr
  deriving Show
type State = (ProgPoint D, Env, Heap, Cont)

instance HasLabel State where
  labelOf (p,_,_,_) = labelOf p

newtype D = D { unD :: State -> Trace D }
instance Eq D where _ == _ = True
instance Show D where show _ = "D"

data Value = Fun D
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "fun"

type instance RetX D = (Val,Value)
type instance StateX D = State
type instance ValX D = NoInfo
type instance App1X D = NoInfo
type instance App2X D = NoInfo
type instance BindX D = NoInfo
type instance LookupX D = NoInfo
type instance UpdateX D = NoInfo

traceLabels :: Trace D -> NonEmpty Label
traceLabels = fmap go . traceStates
  where
    go (Ret _,_,_,_) = returnLabel
    go (E le,_,_,_)  = le.at

traceMemory :: Trace D -> NonEmpty (Env,Heap)
traceMemory = fmap go . traceStates
  where
    go (_,env,heap,_) = (env,heap)

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End p)

type PartialD = State -> Maybe (Trace D)

injD :: D -> PartialD
injD (D d) = \s -> Just (d s)

cons :: State -> Trace D -> Trace D
cons s t = ConsT s (ValA NI) t

step :: PartialD -> D
step fun = D $ \s -> case fun s of
  Nothing -> End s
  Just t  -> cons s t

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \s -> let p = d1 s in p `concatT` d2 (dst p)

run :: LExpr -> Trace D
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

ret :: Value -> PartialD
ret v (E sv,env,heap,cont) | isVal sv = Just (End (Ret (sv,v), env, heap, cont))
ret _ _ = Nothing

var1 :: PartialD
var1 (E (LVar x), env, heap, cont)
  | Just a <- Map.lookup x env
  , Just (e, env', d) <- Map.lookup a heap
  = injD d (E e, env', heap, Update a:cont)
var1 _ = Nothing

var2 :: PartialD
var2 (Ret (sv, v), env, heap, Update a:cont)
  | isVal sv
  = Just (End (Ret (sv,v), env, Map.insert a (sv,env,step d) heap, cont))
  where
    d (E sv',env,heap,cont) | sv'.at == sv.at = Just (End (Ret (sv,v), env, heap, cont))
    d _ = Nothing
var2 _ = Nothing

app1 :: PartialD
app1 (E (LApp e x), env, heap, cont) | Just a <- Map.lookup x env = Just (End (E e, env, heap, Apply a : cont))
app1 _ = Nothing

app2 :: PartialD
app2 (Ret (LLam x e, Fun d), env, heap, Apply a : cont)
  = injD d (E e, Map.insert x a env, heap, cont)
app2 _ = Nothing

let_ :: D -> PartialD
let_ d1 (E (LLet x e1 e2), env,heap,cont)
  | let a = freshAddr heap
  , let env' = Map.insert x a env
  = Just (End (E e2, env', Map.insert a (e1, env', d1) heap, cont))
let_ _ _ = Nothing

