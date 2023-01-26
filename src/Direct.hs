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

module Direct (D(..), maxinf, D3(..), maxinf3, maxinfD) where

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

orElse = flip fromMaybe

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

step :: Action D -> Label -> D -> D
step a l sem = D $ \p -> ConsT (dst p) a $ unD sem $ SnocT p a l

memo :: Trace D -> Label -> D -> D
memo pkey li sem = D $ \pi -> case lookup pkey (consifyT pi) of
  Just pv -> ConsT (dst pi) (LookupA pkey) pv
  Nothing -> unD (step (LookupA pkey) li sem) pi
  where
    lookup pk (ConsT _ a pi')
      | LookupA pk' <- a
      , pk == pk'
      , (pb, Just _) <- splitBalancedPrefix pi'
      ---, trace ("found(" ++ show pk ++ "): " ++ show pb) True
      = valT pb
      | otherwise     = lookup pk pi'
    lookup pk (End l) = Nothing

(!⊥) :: Ord a => (a :-> D) -> a -> D
env !⊥ x = Map.findWithDefault botD x env

maxinfD :: LExpr -> (Name :-> D) -> D
maxinfD le env = D (maxinf le env)

maxinf :: LExpr -> (Name :-> D) -> Trace D -> Trace D
maxinf le env p
  | dst p /= le.at = unD botD p
  | otherwise      = unD (go le env) p
  where
    go :: LExpr -> (Name :-> D) -> D
    go le !env = case le.thing of
      Var n -> env !⊥ n
      App le n -> D $ \p ->
        let p2 = unD (step App1A le.at (go le env)) p
         in concatT p2 $ case val p2 of
              Just (Fun f) -> unD (f (env !⊥ n)) (concatT p p2)
              Nothing      -> unD botD (concatT p p2) -- Stuck! Can happen in an open program
                                                      -- Or with data types
      Lam n le' ->
        let val = Fun (\d -> step App2A (le'.at) (go le' (Map.insert n d env)))
         in D $ \_ -> ConsT le.at (ValA val) (End le.after)
      Let n le1 le2 -> D $ \p ->
        let d = memo p le1.at (go le1 env')
            env' = Map.insert n d env
         in unD (step BindA le2.at (go le2 env')) p

newtype D2 = D2 { unD2 :: (Lifted (Value D2), Trace Void -> Trace Void) }

botD2 :: D2
botD2 = D2 (Bottom, End . dst)

step2 :: Action Void -> Label -> (Trace Void -> Trace Void) -> Trace Void -> Trace Void
step2 a l sem p = ConsT (dst p) a $ sem $ SnocT p a l

--memo2 :: Trace Void -> Label -> (Trace Void -> Trace Void) -> Trace Void -> Trace Void
--memo2 pkey li sem = D $ \pi -> case lookup pkey (consifyT pi) of
--  Just pv -> ConsT (dst pi) (LookupA pkey) pv
--  Nothing -> unD (step (LookupA pkey) li sem) pi
--  where
--    lookup pk (ConsT _ a pi')
--      | LookupA pk' <- a
--      , pk == pk'
--      , (pb, Just _) <- splitBalancedPrefix pi'
--      ---, trace ("found(" ++ show pk ++ "): " ++ show pb) True
--      = valT pb
--      | otherwise     = lookup pk pi'
--    lookup pk (End l) = Nothing

maxinf2 :: LExpr -> (Name :-> D2) -> Trace Void -> Trace Void
maxinf2 le env p
  | dst p /= le.at = snd (unD2 botD2) p
  | otherwise      = snd (unD2 (go le env)) p
  where
    go :: LExpr -> (Name :-> D2) -> D2
    go le !env = case le.thing of
      Var n -> Map.findWithDefault botD2 n env
      App le n ->
        let D2 (v1, t1) = go le env
            D2 (v2, t2) = case v1 of
              Lifted (Fun f) -> f (Map.findWithDefault botD2 n env)
              _              -> botD2
            t p = let p2 = step2 App1A le.at t1 p
                   in concatT p2 (t2 (concatT p p2))
         in D2 (v2, t)
      Lam n le ->
        let
            f d = let D2 (v, t) = go le (Map.insert n d env) in D2 (v,step2 App2A (le.at) t)
            val = Lifted (Fun f)
         in D2 (val, End . dst)
      Let n le1 le2 ->
        let D2 (v1,t1) = go le1 env'
            D2 (v2,t2) = go le2 env'
            d = D2 (v1, step2 (LookupA (End 0)) le1.at t1)
            --d = D2 (v1, memo2 p le1.at (go le1 env') -- WHAT IS p??? Call-by-value/need IMPOSSIBLE!
            env' = Map.insert n d env
         in D2 (v2, step2 BindA le2.at t2)

newtype D3 = D3 { unD3 :: Trace Void -> (Lifted (Value D3), Trace Void) }

botD3 :: D3
botD3 = D3 (\p -> (Bottom, End (dst p)))

step3 :: Action Void -> Label -> D3 -> D3
step3 a l sem = D3 $ \p -> second (ConsT (dst p) a) $ unD3 sem $ SnocT p a l

memo3 :: Trace Void -> Label -> D3 -> D3
memo3 pkey li sem = D3 $ \pi ->
  let (v,po) = unD3 (step3 (LookupA pkey) li sem) pi
  in case lookup pkey (consifyT pi) of
  Just p  -> (v, ConsT (dst pi) (LookupA pkey) p)
  Nothing -> (v,po)
  where
    lookup pk (ConsT _ a pi')
      | LookupA pk' <- a
      , pk == pk'
      , (pb, Just _) <- splitBalancedPrefix pi'
      ---, trace ("found(" ++ show pk ++ "): " ++ show pb) True
      = Just (End (dst pb))
      | otherwise     = lookup pk pi'
    lookup pk (End l) = Nothing

maxinf3 :: LExpr -> (Name :-> D3) -> D3
maxinf3 le env = D3 $ \p ->
  if dst p /= le.at then unD3 botD3 p
                    else unD3 (go le env) p
  where
    go :: LExpr -> (Name :-> D3) -> D3
    go le !env = case le.thing of
      Var n -> Map.findWithDefault botD3 n env
      App le n -> D3 $ \p ->
        let (v,p2) = unD3 (step3 App1A le.at (go le env)) p
         in second (concatT p2) $ case v of
              Lifted (Fun f) -> unD3 (f (Map.findWithDefault botD3 n env)) (concatT p p2)
              _              -> unD3 botD3 (concatT p p2)
      Lam n le ->
        let f d = step3 App2A (le.at) (go le (Map.insert n d env))
         in D3 $ \p -> (Lifted (Fun f), End (dst p))
      Let n le1 le2 -> D3 $ \p ->
        let d = memo3 p le1.at (go le1 env')
            env' = Map.insert n d env
         in unD3 (step3 BindA le2.at (go le2 env')) p

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
  Just (Fun f) -> ByNeed.DFun (absD l . f . concD l)
  Nothing      -> ByNeed.DBot

concD :: Label -> ByNeed.D -> D
concD l ByNeed.DBot     = botD
concD l (ByNeed.DFun f) = undefined -- ⊔{ d | absD l d = V (Fun f) }
 -- Huh, concD is nto well-defined, because those ds might not form a chain.
 -- Ah, but that is just a result of the domain no longer being singleton traces {{π}}.
 -- In the proper powerset lattice we should be fine.
 -- I think we might need to start from the abstract interpreter.
