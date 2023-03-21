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

module Stackless (D(..), ProgPoint(..), Trace, cons, traceLabels, run, runD, State, Env, Heap, Value(..)) where

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
--import qualified Envless

orElse = flip fromMaybe

-- | How we go from Stateful to this state
--
-- 1. Move Lookup into Env; have Env = Name :-> D and let its action look into
--    the Heap. Requires a bit of tricky setup in let_
-- 2. Move the Env to meta level
-- 3. Realise that we can now get rid of the stack, since everything happens
--    on the meta call stack
-- 4. Materialise the state as needed during memo
type State = (ProgPoint D, Heap)
type Env = Name :-> D
type Heap = Addr :-> (LExpr,D)
instance HasLabel State where
  labelOf (p,_) = labelOf p

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
type instance App1X D = NoInfo
type instance ValX D = NoInfo

type instance BindX D = BindInfo
data BindInfo = BI { name :: !Name, addr :: !Addr, denot :: !D } deriving Eq
instance Show BindInfo where show bi = "(" ++ bi.name ++ "↦" ++ show bi.addr ++ ")"

type instance LookupX D = LookupInfo
data LookupInfo = LI { addr :: !Addr } deriving Eq
instance Show LookupInfo where show li = "(" ++ show li.addr ++ ")"

type instance UpdateX D = UpdateInfo
data UpdateInfo = UI { addr :: !Addr } deriving Eq
instance Show UpdateInfo where show ui = "(" ++ show ui.addr ++ ")"

type instance App2X D = App2Info
data App2Info = A2I { name :: !Name, addr :: !Addr } deriving Eq
instance Show App2Info where show ai = "(" ++ show ai.name ++ "↦" ++ show ai.addr ++ ")"

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
      Let n le1 le2 -> D $ \(e,heap) ->
        let addr = Map.size heap
            env' = Map.insert n d env
            d = memo le1 addr (go le1 env')
            heap' = Map.insert addr (le1, d) heap
         in unD (step let_ >.> go le2 env') (e,heap')

ret :: Value -> PartialD
ret v (E sv,heap) | isVal sv = Just (End (Ret (sv, v),heap))
ret _ _ = Nothing

memo :: LExpr -> Addr -> D -> D
memo e a d = step go
  where
    go s@(DVar _,heap) = case Map.lookup a heap of
      Just (sv,d) -> injD (d >.> step (upd a)) (E e, heap)
      Nothing -> error ("invalid address " ++ show a)
    go s = Nothing

upd :: Addr -> PartialD
upd a (Ret (sv,v), heap)
  | isVal sv
  = Just (End (Ret (sv,v), Map.insert a (sv,step (ret v)) heap))
upd _ _ = Nothing

app1 :: PartialD
app1 (DApp e x, heap) = Just (End (E e, heap))
app1 _ = Nothing

app2 :: Name -> LExpr -> PartialD
app2 n e (Ret (sv,v), heap) = Just (End (E e, heap))
app2 n e _ = Nothing

reduce :: D -> D
reduce d = D go
  where
    go s@(Ret (sv,(Fun f)), _) = unD (f d) s
    go s = End s

let_ :: PartialD
let_ (DLet x e1 e2, heap)
  = Just (End (E e2, heap))
let_ _ = Nothing