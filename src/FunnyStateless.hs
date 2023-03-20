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

-- | Although this semantics might seem like it is the stateless semantics
-- associated to CESK, strictly speaking it is not. Note that the Heap contains
-- a D that does Lookup and Update transitions, while the Heap in the CESK
-- semantics does not.
--
-- I tried pushing the lookup and update transitions to the Var case, as for
-- CESK. But that needs to store the start label alongside the expression
-- bound in the heap, e.g., `Heap = Addr :-> (Label, Env, D)`, at which point
-- we can just write `Heap = Addr :-> (LExpr, Env, D)` and we have the
-- actual CESK heap (modulo abstraction of D). Then Update transitions must
-- carry the D as well as the LExpr it denotes, perhaps even the Env.
-- (We *could* recover those from the Value transition just before the Update,
-- but then `materialiseState` would have to do non-trivial stuff wrapping
-- a Fun value into a D (what `ret` does in CESK). I distate that; a disputable
-- judgment call.)
-- Similarly, Bind actions would need to carry the LEXpr and its denotation.
--
-- In short: This semantics was a useful experiment in that it embeds the
-- environment as state, a truly stateless trace semantics. Other than that,
-- it's neither /the/ stateless trace semantics associated to CESK nor is it
-- as simple as (and as thus useful as) the "Direct" semantics.
module FunnyStateless (D(..), Value(..), runInit, run, traceStates) where

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

type Env = Name :-> Addr
type Heap = Addr :-> (Env, D)

type instance AddrOrD D = Addr
newtype instance Value D = Fun (Name,Label,Env,D)

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

snoc :: D -> Label -> Action D -> D
snoc sem l a = D $ \p -> let p' = (unD sem p) in p' `concatT` if dst p' /= l then End (dst p') else ConsT l a (End l)

memo :: Addr -> D -> D
memo a sem = askP $ \pi -> case update a (snocifyT pi) of
  Just (l,v)  -> D (const (ConsT l (ValA v) (End returnLabel)))
  Nothing -> sem
  where
    update addr (SnocT pi' a _)
      | UpdateA addr' <- a
      , addr == addr'
      ---, trace ("found(" ++ show pk ++ "): " ++ show pb) True
      = valT pi'
      | otherwise     = update addr pi'
    update _ End{} = Nothing

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \p -> let p1 = d1 p in p1 `concatT` d2 (p `concatT` p1)

askP :: (Trace D -> D) -> D
askP f = D $ \p -> unD (f p) p

runInit :: LExpr -> Trace D
runInit le = unD (run le) (End le.at)

run :: LExpr -> D
run le = askP $ \p -> case le.thing of
  _ | dst p /= le.at -> botD
  Var n ->
    let (env,heap) = materialiseState p
        (env',d) = lookup n env heap
     in -- trace (n ++ " " ++ showLabel le.at ++ " " ++ show env ++ " " ++ show heap ++ " " ++ show p)
        d
  App le n -> D $ \p ->
    let (env,heap) = materialiseState p
     in case Map.lookup n env of
       Just a ->
        let p2 = unD (cons App1A le.at (run le)) p
            p2' = concatT p p2
         in concatT p2 $ case val p2' of
              Just (Fun (x,l,env',f)) -> unD (cons (App2A x a) l f) p2'
              Nothing      -> unD botD p2' -- Stuck! Can happen in an open program
                                           -- Or with data types
       Nothing -> unD botD p
  Lam n le' -> D $ \p ->
    let (env,_) = materialiseState p
        val = Fun (n,le'.at,env,run le')
     in ConsT le.at (ValA val) (End returnLabel)
  Let n le1 le2 -> D $ \p ->
    let a = hash' p
        d = cons (LookupA a) le1.at (snoc (memo a (run le1)) returnLabel (UpdateA a))
     in unD (cons (BindA n a d) le2.at (run le2)) p
  where
    lookup :: Ord a => a -> (a :-> Addr) -> (Addr :-> (Env,D)) -> (Env,D)
    lookup x env heap = Map.lookup x env >>= (heap Map.!?) `orElse` (Map.empty, botD)

hash' :: Trace D -> Addr
hash' p = Map.size $ snd $ materialiseState p

materialiseState :: Trace D -> (Env, Heap)
materialiseState = go Nothing (Map.empty, Map.empty) . consifyT
  where
    go :: Maybe (Value D) -> (Env, Heap) -> Trace D -> (Env, Heap)
    go _      s             (End l)       = s
    go mb_val s@(env, heap) (ConsT l a t) = case a of
      ValA val -> go (Just val) s t
      BindA n a d | let !env' = Map.insert n a env
        -> go Nothing (env', Map.insert a (env',d) heap) t
      LookupA a | Just (env',_d) <- Map.lookup a heap -> go Nothing (env',heap) t
      App1A     -> go Nothing s t
      UpdateA a | Just (Fun (_x,_l,env',_d)) <- mb_val -> go mb_val (env,Map.adjust (first (const env')) a heap) t
        -- The d stored in the heap is still accurate as it looks for Update
        -- actions in the init trace. Theoretically, we could cough up a d based
        -- on _d from the value, though...
        --
        -- More importantly, we have to update the env', otherwise we don't
        -- sync up with the stateful semantics. E.g., if a let RHS is of the
        -- form `let a = x in λy.a`, then we have to bind the `a` in the value
        -- `λy.a`. Perhaps it would be simpler also to update the d rather than
        -- jsut mess with the env'.
      App2A _n a | Just (Fun (x,_l,env,_d)) <- mb_val -> go Nothing (Map.insert x a env, heap) t

traceStates :: Trace D -> NonEmpty (Env, Heap)
traceStates p = materialiseState <$> prefs p

absD :: Label -> D -> ByNeed.D
absD l (D d) = case val (d (End l)) of
  --Just (Fun f) -> ByNeed.DFun' (absD l . f . concD l)
  Nothing      -> ByNeed.DBot'

concD :: Label -> ByNeed.D -> D
concD l ByNeed.DBot'     = botD
concD l (ByNeed.DFun' f) = undefined -- ⊔{ d | absD l d = V (Fun f) }
 -- Huh, concD is nto well-defined, because those ds might not form a chain.
 -- Ah, but that is just a result of the domain no longer being singleton traces {{π}}.
 -- In the proper powerset lattice we should be fine.
 -- I think we might need to start from the abstract interpreter.
