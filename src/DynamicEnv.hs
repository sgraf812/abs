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

module DynamicEnv (D(..), ProgPoint(..), Trace, traceLabels, traceEnv, run, runD) where

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

-- | How we go from Stateful to this state
--
-- 1. Move Lookup into Env; have Env = Name :-> D and let its action look into
--    the Heap. Requires a bit of tricky setup in let_ and making Fun values go D -> D
-- 2. Move the Env to meta level
-- 3. Realise that we can now get rid of the stack, since everything happens
--    on the meta call stack
-- 4. Materialise the state as needed during memo
type State = (ProgPoint D, Env, Heap, Cont)
type Env = Name :-> D
type Heap = Addr :-> (LExpr,Env,D)
type Cont = [Frame]
data Frame
  = Apply D
  | Update Addr
  deriving Show

instance HasLabel State where
  labelOf (p,_,_,_) = labelOf p

newtype D = D { unD :: State -> Trace D }
newtype Value = Fun (D -> D)
instance Show Value where show (Fun _) = "fun"

--
-- * Action instantiation
--

type instance StateX D = State
type instance RetX D = (Val,Value)
type instance ValX D = NoInfo
type instance App1X D = NoInfo
type instance App2X D = NoInfo
type instance BindX D = NoInfo
type instance LookupX D = NoInfo
type instance UpdateX D = NoInfo

traceEnv :: Trace D -> NonEmpty Env
traceEnv = fmap go . traceStates
  where
    go (_,env,_,_) = env

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End p)

instance Eq D where
  _ == _ = True

instance Ord D where
  compare _ _ = EQ

instance Show D where
  show _ = "D"


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
      Var n -> var
      Lam n le' -> step (ret (Fun (\d -> step (app2 n le' d) >.> go le')))
      App le' n -> step app1 >.> go le' >.> reduce
      Let n le1 le2 -> step (let_ (memo le1 (go le1))) >.> go le2

ret :: Value -> PartialD
ret v (E sv,env,heap,cont) | isVal sv = Just (End (Ret (sv, v),env, heap, cont))
ret _ _ = Nothing

var :: D
var = D $ \s@(e, env, cont,heap) ->
  case e of
    DVar x | Just d <- Map.lookup x env -> unD d s
    _                                   -> End s

memo :: LExpr -> D -> Env -> Addr -> D
memo e d env a = step go
  where
    go s@(DVar _,_,heap,cont) = case Map.lookup a heap of
      Just (sv,env,d) -> injD (d >.> step upd) (E sv, env, heap, Update a : cont)
      Nothing -> error ("invalid address " ++ show a)
    go s = Nothing

upd :: PartialD
upd (Ret (sv,v), env, heap, Update a:cont)
  | isVal sv
  = Just (End (Ret (sv,v), env, Map.insert a (sv,env,step (ret v)) heap, cont))
upd _ = Nothing

app1 :: PartialD
app1 (DApp e x, env, heap, cont) | Just d <- Map.lookup x env = Just (End (E e, env, heap, Apply d : cont))
app1 _ = Nothing

app2 :: Name -> LExpr -> D -> PartialD
app2 n e d (Ret (sv,v), env, heap, Apply _ : cont) = Just (End (E e, Map.insert n d env, heap, cont))
app2 n e d _ = Nothing

reduce :: D
reduce = D go
  where
    go s@(Ret (sv,(Fun f)), _, _, Apply d : cont) = unD (f d) s
    go s = End s

let_ :: (Env -> Addr -> D) -> PartialD
let_ mk_d (DLet x e1 e2, env, heap, cont)
  | let addr = Map.size heap
        env' = Map.insert x d env
        d    = mk_d env' addr
        heap' = Map.insert addr (e1, env', d) heap
  = Just (End (E e2, env', heap', cont))
let_ _ _ = Nothing
