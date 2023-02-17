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

module Stateful (D(..), DExpr(..), Trace, traceLabels, traceEnv, run, runD) where

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
import qualified ByNeed
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

orElse = flip fromMaybe

type State = (DExpr, Env, Cache, Cont)
type Env = Name :-> D
type Cache = Addr :-> Maybe D
type Cont = [Frame]
data Frame
  = Return LExpr Env (Value D)
  | Apply D
  | Update Addr
  deriving Show

newtype D = D { unD :: State -> Trace }
newtype instance Value D = Fun (D -> D)
instance Show (Value D) where
  show (Fun _) = "fun"

type Trace = NonEmpty State

traceLabels :: Trace -> NonEmpty Label
traceLabels = fmap go
  where
    go (Dagger,_,_,_) = daggerLabel
    go (E le,_,_,_)   = le.at

traceEnv :: Trace -> NonEmpty Env
traceEnv = fmap go
  where
    go (_,env,_,_) = env

instance Show DExpr where
  show Dagger = "‡"
  show (E e) = show e.at

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

run :: LExpr -> Trace
run le = unD (runD le) (E le,Map.empty,Map.empty,[])

runD :: LExpr -> D
runD le = D $ \s -> case s of
  (E le',_,_,_) | le.at /= le'.at -> unD botD s
  _                               -> unD (go le) s
  where
    go :: LExpr -> D
    go le = case le.thing of
      Var n -> var
      Lam n le' -> step (ret (Fun (\d -> step (app2 n le' d) >.> go le')))
      App le' n -> step app1 >.> go le' >.> reduce
      Let n le1 le2 -> step (let_ (memo le1 (go le1))) >.> go le2

ret :: Value D -> PartialD
ret v (E sv,env,cont,cache) | isVal sv = [(Dagger, Map.empty, cache, Return v : cont)]
ret _ _ = []

var :: D
var = D $ \s@(e, env, cont,cache) ->
  case e of
    DVar x | Just d <- Map.lookup x env -> unD d s
    _                                   -> NE.singleton s


memo :: LExpr -> D -> Env -> Addr -> D
memo e d env a = step go
  where
    go s@(DVar _,env,cache,cont) = case Map.lookup a cache of
      Just Nothing -> unD (d >.> upd) (E e, env, cache, Update a : cont)
      Just (Just (v,env,d)) -> unD (d >.> upd) (E v, env, cache, Update a : cont)
      Nothing -> error ("invalid address " ++ show a)
    go s = []
    upd s@(Dagger, env, cache, Return val env v : Update a : cont) = _
    upd s = []

var2 :: PartialD
var2 (Dagger, env, heap, cache, Return (sv, env', v):Update a:cont)
  | isVal sv
  , Map.null env
  = [(Dagger, env, Map.insert a (sv,env',step d) heap, Return (sv, env', v):cont, cache)]
  where
    d (E sv',_,heap,cont) | sv'.at == sv.at = [(Dagger, Map.empty, heap, Return (sv, env', v):cont)]
    d _ = []
var2 _ = []

app1 :: PartialD
app1 (DApp e x, env, cache, cont) | Just d <- Map.lookup x env = [(E e, env, cache, Apply d : cont)]
app1 _ = []

app2 :: Name -> LExpr -> D -> PartialD
app2 n e d (Dagger, env, cache, Return (Fun _) : Apply _ : cont) = [(E e, Map.insert n d env, cache, cont)]
app2 n e d _ = []

reduce :: D
reduce = D go
  where
    go s@(Dagger, _, _, Return (Fun f) : Apply d : cont) = unD (f d) s
    go s = NE.singleton s

let_ :: (Addr -> D) -> PartialD
let_ mk_d (DLet x e1 e2, env, cache, cont)
  | (addr,cache') <- alloc cache
  , let env' = Map.insert x (mk_d addr) env
  = [(E e2, env', cache', cont)]
let_ _ _ = []

alloc :: Cache -> (Addr, Cache)
alloc c | let a = Map.size c = (a, Map.insert a Nothing c)
