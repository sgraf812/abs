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

module Stateful (D(..), run, runD, bisimilarForNSteps,
                  State, Env, Heap, Cont, Frame(..), SITrace, Value(..), step, alternativeVar) where

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
import GHC.Stack

orElse = flip fromMaybe

type Heap = Addr :-> (LExpr, Env Addr, D)
type Cont = [Frame]
data Frame
  = Apply Addr
  | Update Addr
  deriving (Eq, Show)
type State = (ProgPoint D, Env Addr, Heap, Cont)

instance HasLabel State where
  labelOf (p,_,_,_) = labelOf p

type SITrace = SemanticallyIrrelevant (Trace D)
newtype D = D { unD :: (SITrace, State) -> Trace D }
instance Eq D where _ == _ = True
instance Show D where show _ = "D"

data Value = Fun (Addr -> D)
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "fun"

type instance RetX D = (Val,Value)
type instance StateX D = State
type instance ValX D = NoInfo
type instance EnvRng D = Addr

type PartialD = (SITrace, State) -> Maybe (Action D, Trace D)

injD :: Action D -> D -> PartialD
injD a (D d) = \(SI p,s) -> Just (a, d (SI (SnocT p a s),s))

step :: HasCallStack => PartialD -> D
step fun = D $ \(SI p,s) -> case fun (SI p,s) of
  Nothing -> End s
  Just (a, ~t)  -> ConsT s a t

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \(SI p1,s) -> let p2 = d1 (SI p1, s) in p2 `concatT` d2 (tgt' (p1 `concatT` p2))

run :: LExpr -> Trace D
run le = unD (runD le) (SI (End s), s)
  where
    s = (E le,Map.empty,Map.empty,[])

apply :: D
apply = D $ \(p, s) -> case s of
  (Ret (_, Fun f), _, _, Apply a:_) -> unD (f a) (p, s)
  _                                 -> End s

runD :: LExpr -> D
runD le = D $ \(p, s) -> case s of
  (E le',_,_,_) | le.at /= le'.at -> error "label mismatch => bottom"
  _                               -> unD (go le) (p, s)
  where
    go :: LExpr -> D
    go le = case le.thing of
      Var n -> step (look n) >.> step upd
      Lam n le' -> step (ret (Fun (\a -> step (app2 le a) >.> go le')))
      App le' n -> step app1 >.> go le' >.> apply
      Let n le1 le2 -> step (let_ (go le1)) >.> go le2

-- | A var case that gives the lookup semantics of an expression based on an
-- address rather than the syntactic name.
alternativeVar :: Addr -> D
alternativeVar a = step (lookAddr a) >.> step upd

ret :: Value -> PartialD
ret v (_, (E sv,env,heap,cont)) | isVal sv = Just (ValA NI, End (Ret (sv,v), env, heap, cont))
ret _ _ = Nothing

look :: Name -> PartialD
look n (p, (E (LVar x), env, heap, cont))
  | n == x
  , Just a <- Map.lookup x env
  , Just (e, env', d) <- Map.lookup a heap
  = injD (LookupA (LI a)) d (p, (E e, env', heap, Update a:cont))
look _ _ = Nothing

lookAddr :: Addr -> PartialD
lookAddr a (p, (E (LVar x), env, heap, cont))
  | Just a' <- Map.lookup x env
  , a == a'
  , Just (e, env', d) <- Map.lookup a heap
  = injD (LookupA (LI a)) d (p, (E e, env', heap, Update a:cont))
lookAddr _ _ = Nothing

upd :: PartialD
upd (_, (Ret (sv, v), env, heap, Update a:cont))
  | isVal sv
  = Just (UpdateA (UI a), End (Ret (sv,v), env, Map.insert a (sv,env,step d) heap, cont))
  where
    d (_, (E sv',env,heap,cont)) | sv'.at == sv.at = Just (ValA NI, End (Ret (sv,v), env, heap, cont))
    d _ = Nothing
upd _ = Nothing

app1 :: PartialD
app1 (_, (E (LApp e x), env, heap, cont)) | Just a <- Map.lookup x env = Just (App1A (A1I a), End (E e, env, heap, Apply a : cont))
app1 _ = Nothing

app2 :: LExpr -> Addr -> PartialD
app2 le a (p, (Ret (le'@(LLam x e), Fun f), env, heap, Apply a' : cont))
  | le.at == le'.at, a == a'
  = Just (App2A (A2I x a), End (E e, Map.insert x a env, heap, cont))
app2 _ _ _ = Nothing

let_ :: D -> PartialD
let_ d1 (_, (E (LLet x e1 e2), env,heap,cont))
  | let a = freshAddr heap
  , let env' = Map.insert x a env
  = Just (BindA (BI x e1 a d1), End (E e2, env', Map.insert a (e1, env', d1) heap, cont))
let_ _ _ = Nothing

firstDiff :: Trace D -> Trace D -> Maybe ((State,State), (State,State))
firstDiff p1 p2 = find (uncurry (/=)) $ zip ss1 ss2
  where
    s1 = toList $ traceStates p1
    ss1 = zip s1 (tail s1)
    s2 = toList $ traceStates p2
    ss2 = zip s2 (tail s2)

-- | Run 2 states in parallel and see if they produce the same trace (as far as
-- labels are concerned), up to a certain length.
bisimilarForNSteps :: Int -> Trace D -> Trace D -> Bool
bisimilarForNSteps n p1 p2 = case (continue p1, continue p2) of
  --(Just p1', Just p2') -> s p1' p2' $ traceLabels p1' == traceLabels p2'
  (Just p1', Just p2') -> traceLabels p1' == traceLabels p2'
  (Nothing, Nothing)   -> True  -- can't handle return states
  _                    -> False -- one p1 resulted in a return state
  where
    continue p | (E le, _, _ , _) <- tgt p = Just (takeT n $ unD (runD le) (tgt' p))
               | otherwise                 = Nothing
    s p1 p2 = case (firstDiff p1 p2) of
      Just ((s11,s12), (s21, s22)) -> trace (assert (s11 == s21) "\n" ++ show s11 ++ "\n\n" ++ show s12 ++ "\n" ++ show s22 ++ "\n")
      Nothing -> id
