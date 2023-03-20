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

module Stackless (D(..), ProgPoint(..), Trace, traceLabels, run, runD) where

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
import qualified Envless

orElse = flip fromMaybe

-- | How we go from Stateful to this state
--
-- 1. Move Lookup into Env; have Env = Name :-> D and let its action look into
--    the Cache, getting rid of the Heap. Requires a bit of tricky setup in let_
-- 2. Move the Env to meta level
-- 3. Realise that we can now get rid of the stack, since everything happens
--    on the meta call stack
-- 4. Materialise the state as needed during memo
type State = (ProgPoint (Val,Value D), Cache)
type Env = Name :-> D
type Cache = Addr :-> Maybe (Val,D)

newtype D = D { unD :: State -> Trace }
newtype instance Value D = Fun (D -> D)
instance Show (Value D) where
  show (Fun _) = "fun"

type Trace = NonEmpty State

traceLabels :: Trace -> NonEmpty Label
traceLabels = fmap go
  where
    go (Ret _,_) = returnLabel
    go (E le,_)  = le.at

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
    con s@(e,_) []      ((e',_) NE.:| t2) = assert (eqPoint e e') t2
    con _         (s':t1) t2                  = s' : con s' t1 t2

-- | Empty list is Nothing (e.g., undefined), non-empty list is Just
type MaybeSTrace = [State]

type PartialD = State -> MaybeSTrace

askS :: (State -> D) -> D
askS f = D $ \s -> unD (f s) s

injD :: D -> PartialD
injD (D d) = \s -> NE.toList (d s)

step :: PartialD -> D
step fun = D $ \s -> s NE.:| fun s

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \s -> let p = d1 s in p `concatS` d2 (dstS p)

run :: LExpr -> Trace
run le = unD (runD le) (E le,Map.empty)

runD :: LExpr -> D
runD le = D $ \s -> case s of
  (E le',_) | le.at /= le'.at -> unD botD s
  _                             -> unD (go le Map.empty) s
  where
    go :: LExpr -> Env -> D
    go le env = case le.thing of
      Var n -> env Map.!? n `orElse` botD
      Lam n le' -> step (ret (Fun (\d -> step (app2 n le') >.> go le' (Map.insert n d env))))
      App le' n -> step app1 >.> go le' env >.> reduce (env Map.! n)
      Let n le1 le2 -> D $ \(e,cache) ->
        let (addr,cache') = alloc cache
            d = memo le1 addr (go le1 env')
            env' = Map.insert n d env
         in unD (step let_ >.> go le2 env') (e,cache')

ret :: Value D -> PartialD
ret v (E sv,cache) | isVal sv = [(Ret (sv, v),cache)]
ret _ _ = []

memo :: LExpr -> Addr -> D -> D
memo e a d = step go
  where
    go s@(DVar _,cache) = case Map.lookup a cache of
      Just Nothing -> injD (d >.> step (upd a)) (E e, cache)
      Just (Just (sv,d)) -> injD (d >.> step (upd a)) (E sv, cache)
      Nothing -> error ("invalid address " ++ show a)
    go s = []

upd :: Addr -> PartialD
upd a (Ret (sv,v), cache)
  | isVal sv
  = [(Ret (sv,v), Map.insert a (Just (sv,step (ret v))) cache)]
upd _ _ = []

app1 :: PartialD
app1 (DApp e x, cache) = [(E e, cache)]
app1 _ = []

app2 :: Name -> LExpr -> PartialD
app2 n e (Ret (sv,v), cache) = [(E e, cache)]
app2 n e _ = []

reduce :: D -> D
reduce d = D go
  where
    go s@(Ret (sv,(Fun f)), _) = unD (f d) s
    go s = NE.singleton s

let_ :: PartialD
let_ (DLet x e1 e2, cache)
  = [(E e2, cache)]
let_ _ = []

alloc :: Cache -> (Addr, Cache)
alloc c | let a = Map.size c = (a, Map.insert a Nothing c)
