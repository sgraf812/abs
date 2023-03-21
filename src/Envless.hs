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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

module Envless (D(..), ProgPoint(..), Trace, traceLabels, run, runD) where

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

-- | How we go from Stateful to this state
--
-- 1. Move Lookup into Env; have Env = Name :-> D and let its action look into
--    the Heap. Requires a bit of tricky setup in let_
-- 2. Move the Env to meta level
-- 3. Realise that we can now get rid of the stack, since everything happens
--    on the meta call stack
-- 4. Materialise the state as needed during memo
type State = (ProgPoint D, Heap, Cont)
type Env = Name :-> D
type Heap = Addr :-> (LExpr,D)
type Cont = [Frame]
data Frame
  = Apply D
  | Update Addr
  deriving Show

instance HasLabel State where
  labelOf (p,_,_) = labelOf p

newtype D = D { unD :: State -> Trace D }
instance Eq D where _ == _ = True
instance Show D where show _ = "D"
newtype Value = Fun (D -> D)
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "fun"

--
-- * Action instantiation
--

type instance StateX D = State
type instance RetX D = (Val,Value)
type instance ValX D = NoInfo
type instance EnvRng D = D

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End p)

type PartialD = State -> Maybe (Trace D)

injD :: D -> PartialD
injD (D d) = \s -> Just (d s)

cons :: State -> Trace D -> Trace D
cons s t = ConsT s (ValA NI) t

step :: Action D -> PartialD -> D
step a fun = D $ \s -> case fun s of
  Nothing -> End s
  Just t  -> ConsT s a t

whenP :: Maybe a -> (a -> D) -> D
whenP Nothing  _ = botD
whenP (Just a) d = d a

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \s -> let p = d1 s in p `concatT` d2 (dst p)

run :: LExpr -> Trace D
run le = unD (runD le) (E le,Map.empty,[])

runD :: LExpr -> D
runD le = D $ \s -> case s of
  (E le',_,_) | le.at /= le'.at -> unD botD s
  _                             -> unD (go le Map.empty) s
  where
    go :: LExpr -> Env -> D
    go le env = case le.thing of
      Var n -> env Map.!? n `orElse` botD
      Lam n le' ->
        let v = Fun (\d -> step (App2A (AI n d)) (app2 n le') >.> go le' (Map.insert n d env))
         in step (ValA NI) (ret v)
      App le' n -> whenP (Map.lookup n env) $ \d ->
        step (App1A NI) (app1 d) >.> go le' env >.> reduce
      Let n le1 le2 -> D $ \(e,heap,cont) ->
        let addr = Map.size heap
            env' = Map.insert n (memo le1 addr d) env
            d = go le1 env'
            heap' = Map.insert addr (le1, d) heap
         in unD (step (BindA (BI n le1 addr d)) let_ >.> go le2 env') (e,heap',cont)

ret :: Value -> PartialD
ret v (E sv,heap,cont) | isVal sv = Just (End (Ret (sv, v),heap, cont))
ret _ _ = Nothing

memo :: LExpr -> Addr -> D -> D
memo e a d = step (LookupA (LI a)) go
  where
    go s@(DVar _,heap,cont) = case Map.lookup a heap of
      Just (sv,d) -> injD (d >.> step (UpdateA (UI a)) upd) (E sv, heap, Update a : cont)
      Nothing -> error ("invalid address " ++ show a)
    go s = Nothing

upd :: PartialD
upd (Ret (sv,v), heap, Update a:cont)
  | isVal sv
  = Just (End (Ret (sv,v), Map.insert a (sv,step (ValA NI) (ret v)) heap, cont))
upd _ = Nothing

app1 :: D -> PartialD
app1 d (DApp e x, heap, cont) = Just (End (E e, heap, Apply d : cont))
app1 d _ = Nothing

app2 :: Name -> LExpr -> PartialD
app2 n e (Ret (sv,v), heap, Apply _ : cont) = Just (End (E e, heap, cont))
app2 n e _ = Nothing

reduce :: D
reduce = D go
  where
    go s@(Ret (sv,(Fun f)), _, Apply d : cont) = unD (f d) s
    go s = End s

let_ :: PartialD
let_ (DLet x e1 e2, heap, cont)
  = Just (End (E e2, heap, cont))
let_ _ = Nothing
