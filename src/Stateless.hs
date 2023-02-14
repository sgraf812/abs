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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Stateless (D(..), Value(..), maxinf, maxinfD, absS, snoc) where

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
import qualified ByNeed
import Data.Void
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)

orElse = flip fromMaybe
infixl 1 `orElse`

type instance AddrOrD D = Addr
data instance Value D = Fun D

instance Show (Value D) where
  show (Fun _) = "fun"

instance Eq (Value D) where
  _ == _ = True

instance Ord (Value D) where
  compare _ _ = EQ

-- | Finite intialisation trace to infinite or maximal finite trace.
--
-- This type is actually the subtype of `Trace -> Trace` for which every
-- inhabitant `d` satisfies `src(d(p)) = dst(p)`.
--
-- We can give a partial pointwise prefix order ⊑:
--
-- d1(p) ⊑ d2(p)  <=>  ∃p'. d1(p) `concatT` p' = d2(p)
--
-- Note that a `D` is *not* a monotone map.
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

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End (dst p))

-- | The partial pointwise prefix order. Can't compute :(
leqD :: D -> D -> Bool
leqD d1 d2 = forall (\p -> unD d1 p `isPrefixOf` unD d2 p)
  where
    forall f = undefined -- would need to iterate over all Traces
    t1 `isPrefixOf` t2 = case (consifyT t1, consifyT t2) of
      (End l, ConsT l' _ _) -> l == l'
      (ConsT l _ t, ConsT l' _ t') -> l == l' && t1 `isPrefixOf` t2
      (_,_) -> False

-- | The pairwise lub on ordered `D`s. Undefined everywhere else
lubD :: D -> D -> D
lubD d1 d2 = if d1 `leqD` d2 then d2 else d1

instance Eq D where
  _ == _ = True

instance Ord D where
  compare _ _ = EQ

instance Show D where
  show _ = "D"

cons :: Action D -> Label -> D -> D
cons a l sem = D $ \p -> ConsT (dst p) a $ unD sem $ SnocT p a l

snoc :: D -> Action D -> D
snoc sem a = D $ \p -> let p' = (unD sem p) in SnocT p' a (dst p')

memo :: Addr -> D -> D
memo a sem = D $ \pi -> case lookup a (consifyT pi) of
  Just pv -> pv
  Nothing -> unD sem pi
  where
    lookup pk (ConsT _ a pi')
      | LookupA pk' <- a
      , pk == pk'
      , (pb, Just _) <- splitBalancedPrefix pi'
      ---, trace ("found(" ++ show pk ++ "): " ++ show pb) True
      = valT pb
      | otherwise     = lookup pk pi'
    lookup pk (End l) = Nothing

type Env = Name :-> Addr
type Heap = Addr :-> (Env, D)

maxinfD :: LExpr -> (Name :-> D) -> D
maxinfD le env = D (maxinf le env)

maxinf :: LExpr -> Trace D -> Trace D
maxinf le p
  | dst p /= le.at = unD botD p
  | otherwise      = unD (go le) p
  where
    go :: LExpr -> D
    go le = case le.thing of
      Var n -> D $ \p ->
        let (env,heap) = materialiseState p
         in env !⊥ n
      App le n -> D $ \p ->
        let p2 = unD (cons (App1A n) le.at (go le env)) p
         in concatT p2 $ case val p2 of
              Just (Fun f) -> unD (f (env !⊥ n)) (concatT p p2)
              Nothing      -> unD botD (concatT p p2) -- Stuck! Can happen in an open program
                                                      -- Or with data types
      Lam n le' ->
        let val = Fun (\d -> cons (App2A n d) (le'.at) (go le' (Map.insert n d env)))
         in D $ \_ -> ConsT le.at (ValA val) (End le.after)
      Let n le1 le2 -> D $ \p ->
        let a = hash p
            d = cons (LookupA a) le1.at (snoc (memo a (go le1 env')) (UpdateA a))
            env' = Map.insert n d env
         in unD (cons (BindA n a d) le2.at (go le2 env')) p
    lookup :: Ord a => a -> (a :-> Addr) -> (Addr :-> D) -> D
    lookup x env heap = Map.lookup x env >>= (heap Map.!?) `orElse` botD

materialiseState :: Trace D -> (Env, Heap)
materialiseState = go [] (Map.empty, Map.empty) . consifyT
  where
    go :: [Env] -> (Env, Heap) -> Trace D -> (Env, Heap)
    go stk s             (End l)       = s
    go stk s@(env, heap) (ConsT l a t) = case a of
      ValA{} -> go stk s t
      BindA n a d | let !env' = Map.insert n a env
        -> go stk (env', Map.insert a (env',d) heap) t
      LookupA _ -> go (env:stk) s t
      App1A _ -> go (env:stk) s t
      UpdateA a | env':stk' <- stk -> (env', heap)
        -- The d stored in the heap is still accurate
        -- as it looks for Update actions in the init
        -- trace
      App2A n a | env':stk' <- stk -> (Map.insert n a env', heap)

-- Stateful semantics, Mk II:
-- Add layer of indirection for *all* Ds, put D in the cache, which is now a heap
-- Then represent heap entries by closures, Done! CESK/Sestoft Mk III
data ElabFrame = Appl !Addr | Upda !Addr deriving (Eq, Show)
type ElabStack = [ElabFrame]

type Configu = (Addr:->D, Label, Name :-> Addr, ElabStack)

-- | Abstraction function to stateful maximal trace semantics
absS :: Trace D -> [Configu]
absS p = map (go . snocifyT) (prefs (traceShowId p))
  where
    go :: Trace D -> Configu
    go (End l) = (Map.empty, l, Map.empty, [])
    go p0@(SnocT p a l) =
      let (_, _, _, s) = go p in
      let env = varrho p0 in
      let (_, heap) = varheap p0 in
      case a of -- TODO: What if l /= l'?
        ValA v -> (heap, l, env, s)
        App1A n -> (heap, l, env, Appl (env Map.! n):s)
        App2A n _ | let (Appl d : s') = s -> (heap, l, env, s')
        LookupA addr -> (heap, l, env, Upda addr:s)
        UpdateA addr
          | let (Upda addr' : s') = s
          -> assert (addr == addr') (updateHeap heap addr' p, l, env, s')
        BindA n addr d -> (heap, l, env, s)

    varrho (End l) = Map.empty
    varrho (SnocT p a _) = case a of
      BindA n addr d -> Map.insert n addr (varrho p)
      App1A _ -> varrho p
      App2A n d | SnocT p' (App1A n') _ <- skipApp1 p, let addr = varrho p' Map.! n' -> Map.insert n addr (varrho (skipUpdates p))
      LookupA addr -> varrho (defn addr p)
      UpdateA addr -> varrho (skipLookup addr p)
      ValA v -> varrho p

    defn addr p@(SnocT _ (BindA _ addr' _) _) | addr == addr' = p
    defn addr (SnocT p _ _) = defn addr p
    defn addr (End _) = error $ "no defn " ++ show addr

    skipLookup addr (SnocT p (LookupA addr') _) | addr == addr' = p
    skipLookup addr (SnocT p _ _) = skipLookup addr p
    skipLookup addr (End _) = error $ "no defn " ++ show addr

    skipUpdates (SnocT p (UpdateA _) _) = skipUpdates p
    skipUpdates p@(SnocT _ (ValA _) _) = p
    skipUpdates p = error (show p)

    skipApp1 p0@(SnocT p a _) = case a of
      App1A{} -> p0
      UpdateA addr -> skipApp1 $ skipLookup addr p
      App2A{} | (SnocT p' _ _) <- skipApp1 p -> skipApp1 p'
      ValA{} -> skipApp1 p
      LookupA{} -> error "what"
      BindA{} -> skipApp1 p

    unwindUntil pred p@(SnocT _ a _) | pred a = Just p
    unwindUntil pred (SnocT p _ _) = unwindUntil pred p
    unwindUntil pred (End _) = Nothing

    varheap (End l) = (undefined, Map.empty)
    varheap (SnocT p a l) =
      let (d,heap') = varheap p in
      case a of
        ValA v -> (D $ const $ SnocT (End (dst p)) a l, heap')
        UpdateA addr -> (d, Map.insert addr d heap')
        BindA n addr d -> (undefined, Map.insert addr d heap')
        LookupA addr -> (undefined, heap')
        App1A _ -> (undefined, heap')
        App2A{} -> (undefined, heap')

    updateHeap heap addr (SnocT p UpdateA{} _) = updateHeap heap addr p
    updateHeap heap addr (SnocT p a@ValA{} l2) = Map.insert addr (D $ const $ SnocT (End (dst p)) a l2) heap
    updateHeap heap addr p = error $ show heap ++ show addr ++ show p


-- | Derive the pointwise prefix trace semantics from a maximal and inifinite
-- trace semantics (Section 6.12 of POAI).
pointwise :: LExpr -> Trace D -> Label -> [Trace D]
pointwise e p l = map (concatT p) $ tracesAt l $ maxinf e Map.empty p

-- post(go le []) will be the reachability semantics, e.g., small-step!
-- Wart: Instead of a (set of) Trace `t`, it should take a (set of) Configuration `c`
-- such that `config p = c` (that is, we don't know how to efficiently compute
-- the concretisation function γ(cs) = ts). By doing it this way, we can
-- actually compute.
-- The lifting to sets (of initialisation Traces/Configurations) is routine.
-- we return a list instead of a set, because it might be infinite and we want to
-- enumerate.
post :: LExpr -> Trace D -> Label -> [[ByNeed.Configuration]]
post e p l = map (ByNeed.config (unlabel e)) (pointwise e p l)

absD :: Label -> D -> ByNeed.D
absD l (D d) = case val (d (End l)) of
  Just (Fun f) -> ByNeed.DFun' (absD l . f . concD l)
  Nothing      -> ByNeed.DBot'

concD :: Label -> ByNeed.D -> D
concD l ByNeed.DBot'     = botD
concD l (ByNeed.DFun' f) = undefined -- ⊔{ d | absD l d = V (Fun f) }
 -- Huh, concD is nto well-defined, because those ds might not form a chain.
 -- Ah, but that is just a result of the domain no longer being singleton traces {{π}}.
 -- In the proper powerset lattice we should be fine.
 -- I think we might need to start from the abstract interpreter.
