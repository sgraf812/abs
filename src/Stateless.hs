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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MonoLocalBinds #-}

module Stateless (D(..), Value(Fun), runInit, run, runD) where

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
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import GHC.Stack
import qualified Stateful
import qualified Stackless

-- | Finite intialisation trace to infinite or maximal finite trace.
--
-- This type is actually the subtype of `Trace -> Trace` for which every
-- inhabitant `d` satisfies `src(d(p)) = dst(p)`.
--
-- We can give a partial pointwise prefix order ⊑:
--
-- d1(p) ⊑ d2(p)  <=>  ∃p'. d1(p) `concatT` p' = d2(p)
--
-- Note that a `D` is *not* a monotone map; indeed our semantics isn't.
-- The ordering is to be understood pointwise, ⊑^. .
--
-- There exists a bottom element `⊥(p) = End (dst p)` and directed sets have a
-- the pointwise supremum ⊔^.
-- (Finite case is simply the max element; infinite case is the limit of the
-- prefix traces).
-- Thus, (D,⊑^.,⊥,⊔^.) forms a CPO with bottom element ⊥.
-- Note that ⊥ represents an expression that is stuck in every context;
-- values do at least another step in our semantics.
--
newtype D = D { unD :: Trace D -> Trace D }
instance Eq D where _ == _ = True
instance Show D where show _ = "D"

newtype Value = Fun (D -> D)
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "fun"

--
-- * Action instantiation
--

type instance StateX D = ProgPoint D
type instance RetX D = NoInfo
type instance ValX D = Value
type instance EnvRng D = D

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End (dst p))

concatD :: HasCallStack => D -> D -> D
concatD (D d1) (D d2) = D $ \p -> let p1 = d1 p in p1 `concatT` d2 (p `concatT` p1)
infixr 5 `concatD`

(>.>) :: HasCallStack => D -> D -> D
(>.>) = concatD

askP :: (Trace D -> D) -> D
askP f = D $ \p -> unD (f p) p

whenP :: Maybe a -> (a -> D) -> D
whenP Nothing  _ = botD
whenP (Just a) d = d a

whenAtP :: ProgPoint D -> D -> D
whenAtP l d = askP $ \p -> if labelOf l == labelOf (dst p) then d else botD

step :: Action D -> ProgPoint D -> D
step a l = D $ \p -> ConsT (dst p) a (End l)

stepm :: ProgPoint D -> Action D -> ProgPoint D -> D
stepm l1 a l2 = whenAtP l1 (step a l2)

memo :: Addr -> ProgPoint D -> D -> D
memo a p sem = askP $ \pi ->
  let (p', d) = case update a (snocifyT pi) of
        Just (p', v) -> (p', step (ValA v) (Ret NI))
        Nothing      -> (p, sem)
      update addr (SnocT pi' a _)
        | UpdateA ui <- a :: Action D
        , addr == ui.addr
        = valT pi'
        | otherwise
        = update addr pi'
      update _ End{} = Nothing
  in wrapLookup a p' d

wrapLookup :: Addr -> ProgPoint D -> D -> D
wrapLookup a p d =
  step (LookupA (LI a)) p >.> d >.> stepm (Ret NI) (UpdateA (UI a)) (Ret NI)

runD :: LExpr -> (Name :-> D) -> D
runD le env = go le env
  where
    (!⊥) :: Ord a => (a :-> D) -> a -> D
    env !⊥ x = Map.findWithDefault botD x env
    go :: LExpr -> (Name :-> D) -> D
    go le !env = whenAtP (E le) $ case le.thing of
      Var n -> env !⊥ n
      App le n -> whenP (Map.lookup n env) $ \d ->
        let apply = askP $ \p -> whenP (val p) $ \(Fun f) -> f d
         in step (App1A NI) (E le) >.> go le env >.> apply
      Lam n le' ->
        let val = Fun (\d -> step (App2A (AI n d)) (E le') >.> go le' (Map.insert n d env))
         in step (ValA val) (Ret NI)
      Let n le1 le2 -> askP $ \p ->
        let a = hash p
            d = memo a (E le1) (go le1 env')
            env' = Map.insert n d env
         in step (BindA (BI n le1 a d)) (E le2) >.> go le2 env'

run :: LExpr -> (Name :-> D) -> Trace D -> Trace D
run le env p = unD (runD le env) p

runInit :: LExpr -> Trace D
runInit le = run le Map.empty (End (E le))

absStackD :: Stateless.D -> Stackless.D
absStackD (Stateless.D d) = Stackless.D $
  \s -> absStackTrace (d (concStackState s))

concStackD :: Stackless.D -> Stateless.D
concStackD (Stackless.D d) = D $ \p -> concStackTrace (d (dst (absStackTrace p)))

absStackV :: Stateless.Value -> Stackless.Value
absStackV (Fun f) = Stackless.Fun (absStackD . f . concStackD)

concStackV :: Stackless.Value -> Stateless.Value
concStackV (Stackless.Fun f) = Fun (concStackD . f . absStackD)

concStackState :: Stackless.State -> Trace D
concStackState (Ret (sv,_), heap) = go (End (E sv)) (Map.toList heap)
  where
    dummyLabel = -1
    go inner ((a,(e,d)):rest) = go (ConsT (E (Lab dummyLabel (Var "x"))) (BindA (BI "x" e a (concStackD d)) :: Action D) inner) rest

concStackTrace :: Trace Stackless.D -> Trace D
concStackTrace t = go t
  where
    forget_ret = mapProgPoint (const NI)
    go (End (p,heap)) = End (forget_ret p)
    go (ConsT (p,heap) a rest) =
      ConsT (forget_ret p) a' (go rest)
        where
          (p',_) = src rest
          a' = case (p, a, p') of
            (_, ValA _, Ret (_, v)) -> ValA (concStackV v)
            (_, UpdateA ui, _) -> UpdateA ui
            (_, LookupA li, _) -> LookupA li
            (_, BindA bi, _) -> BindA (bi { denot = concStackD bi.denot })
            (_, App1A _, _) -> App1A NI
            (_, App2A ai, _) -> App2A (ai { arg = concStackD ai.arg })

absStackTrace :: Trace Stateless.D -> Trace Stackless.D
absStackTrace p = go Map.empty Map.empty Map.empty (toList (splitsT p))
  where
    mk_state_at :: ProgPoint D -> Trace Stateless.D -> Stackless.Heap -> Stackless.State
    mk_state_at p pref heap
      | Ret NI <- p, let Just (E sv,v) = valT pref
      = (Ret (sv, absStackV v), heap)
      | E e <- p
      = (E e, heap)
    go :: (Addr :-> Stackless.Env) -> Stackless.Env -> Stackless.Heap -> [(Trace Stateless.D,Trace Stateless.D)] -> Trace Stackless.D
    go envs env heap ((pref,suff):rest) = case suff of
      End l -> End (mk_state_at l pref heap)
      ConsT l a p -> mk_state_at l pref heap `Stackless.cons` case a of
        BindA bi ->
          let env' = Map.insert bi.name (absStackD bi.denot) env
              envs' = Map.insert bi.addr env' envs
              heap' = Map.insert bi.addr (bi.rhs, absStackD bi.denot)
           in go envs' env' heap rest
        LookupA a -> go envs (envs Map.! a.addr) heap rest
        UpdateA a ->
          let Just (E sv,v) = valT pref
              d = wrapLookup a.addr (E sv) (step (ValA v) (Ret NI))
           in go (Map.insert a.addr env envs) env (Map.insert a.addr (sv, absStackD d) heap) rest
        ValA v ->
          go envs env heap rest
        App1A _ ->
          go envs env heap rest
        App2A ai ->
          go envs (Map.insert ai.name (absStackD ai.arg) env) heap rest

--config :: Show d => Expr -> Trace d -> [Configuration]
--config e p0 = yield (consifyT p0) init
--  where
--    init = (Map.empty, e, [])
--    traceIt f res = trace (f res) res
--    yield t c = c : go t c
--    go (End l) _ = []
--    go (ConsT l a p) c0@(h, Fix e, s) = -- trace ("her " ++ unlines [show c0, show a, show p]) $
--      case a of
--        ValA _ -> go p c0 -- No corresponding small-step transition
--        BindA{}      | Let n e1 e2 <- e ->
--          let n' = freshName n h
--              e1' = subst n n' e1
--              e2' = subst n n' e2
--              c1 = (Map.insert n' e1' h, e2', s)
--           in yield p c1
--        App1A        | App e n <- e ->
--          let c1 = (h, e, Apply n:s)
--              (p1,~(Just (ConsT l App2A{} p2))) = splitBalancedPrefix p
--              cs1 = yield p1 c1
--              (h',Fix (Lam m eb),Apply n':s') = last cs1
--              c2 = (h', subst m n' eb, s')
--              cs2 = yield p2 c2
--           in -- trace ("app1: " ++ unlines [show c1,show p, show p1, show p2]) $
--              cs1 ++ cs2
--
--        LookupA _    | Var n <- e ->
--          let c1 = (h, h Map.! n, Update n:s)
--              (p1,mb_p2) = splitBalancedPrefix p
--              cs1 = yield p1 c1
--              (h',e',Update n':s') = last cs1
--              c2 = (Map.insert n' e' h', e', s')
--              cs2 = case mb_p2 of
--                Just (ConsT l UpdateA{} p2) -> yield p2 c2
--                _                           -> []
--           in -- trace ("look: " ++ show c1 ++ show (takeT 4 p1)) $
--              cs1 ++ cs2
--
--        _ -> -- trace (show l ++ " " ++ show a ++ " " ++ show (Fix e) ++ "\n"  ++ show (takeT 20 p0) ++ "\n" ++ show (takeT 20 p))
--             []
