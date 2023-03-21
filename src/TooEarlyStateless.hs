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

-- | Although this semantics might seem like it is the stateless semantics
-- associated to Stateful, strictly speaking it is not. Note that the Heap contains
-- a D that does Lookup and Update transitions, while the Heap in the Stateful
-- semantics does not.
--
-- I tried pushing the lookup and update transitions to the Var case, as for
-- Stateful. But that needs to store the start label alongside the expression
-- bound in the heap, e.g., `Heap = Addr :-> (ProgPoint D, Env, D)`, at which point
-- we can just write `Heap = Addr :-> (LExpr, Env, D)` and we have the
-- actual Stateful heap (modulo abstraction of D). Then Update transitions must
-- carry the D as well as the LExpr it denotes, perhaps even the Env.
-- (We *could* recover those from the Value transition just before the Update,
-- but then `materialiseState` would have to do non-trivial stuff wrapping
-- a Fun value into a D (what `ret` does in Stateful). I distate that; a disputable
-- judgment call.)
-- Similarly, Bind actions would need to carry the LEXpr and its denotation.
--
-- In short: This semantics was a useful experiment in that it embeds the
-- environment as state, a truly stateless trace semantics. Other than that,
-- it's neither /the/ stateless trace semantics associated to Stateful nor is it
-- as simple as (and as thus useful as) the "Stateless" semantics.
module TooEarlyStateless (D(..), Value(..), runInit, run, materialiseStates) where

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

type Env = Name :-> Addr
type Heap = Addr :-> (Env, D)

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
instance Eq D where _ == _ = True
instance Show D where show _ = "D"

newtype Value = Fun (Name,LExpr,Env,D)
instance Eq Value where _ == _ = True
instance Show Value where show (Fun _) = "fun"

--
-- * Action instantiation
--

type instance StateX D = ProgPoint D
type instance RetX D = NoInfo
type instance ValX D = Value
type instance EnvRng D = Addr

-- | The bottom element of the partial pointwise prefix ordering on `D`.
botD :: D
botD = D (\p -> End (dst p))

cons :: Action D -> ProgPoint D -> D -> D
cons a l sem = D $ \p -> ConsT (dst p) a $ unD sem $ SnocT p a l

snoc :: D -> ProgPoint D -> Action D -> D
snoc sem l a = D $ \p -> let p' = (unD sem p) in p' `concatT` if dst p' /= l then End (dst p') else ConsT l a (End l)

memo :: Addr -> D -> D
memo a sem = askP $ \pi -> case update a (snocifyT pi) of
  Just (l,v)  -> D (const (ConsT l (ValA v) (End (Ret NI))))
  Nothing -> sem
  where
    update :: Addr -> Trace D -> Maybe (ProgPoint D, Value)
    update addr (SnocT pi' a _)
      | UpdateA ai <- a
      , addr == ai.addr
      ---, trace ("found(" ++ show pk ++ "): " ++ show pb) True
      = valT pi'
      | otherwise     = update addr pi'
    update _ End{} = Nothing

(>.>) :: D -> D -> D
D d1 >.> D d2 = D $ \p -> let p1 = d1 p in p1 `concatT` d2 (p `concatT` p1)

askP :: (Trace D -> D) -> D
askP f = D $ \p -> unD (f p) p

runInit :: LExpr -> Trace D
runInit le = unD (run le) (End (E le))

run :: LExpr -> D
run le = askP $ \p -> case le.thing of
  _ | dst p /= E le -> botD
  Var n ->
    let (env,heap) = materialiseState p
        (env',d) = lookup n env heap
     in -- trace (n ++ " " ++ showLabel le.at ++ " " ++ show env ++ " " ++ show heap ++ " " ++ show p)
        d
  App le n -> D $ \p ->
    let (env,heap) = materialiseState p
     in case Map.lookup n env of
       Just a ->
        let p2 = unD (cons (App1A NI) (E le) (run le)) p
            p2' = concatT p p2
         in concatT p2 $ case val p2' of
              Just (Fun (x,l,env',f)) -> unD (cons (App2A (AI x a)) (E l) f) p2'
              Nothing      -> unD botD p2' -- Stuck! Can happen in an open program
                                           -- Or with data types
       Nothing -> unD botD p
  Lam n le' -> D $ \p ->
    let (env,_) = materialiseState p
        val = Fun (n,le',env,run le')
     in ConsT (E le) (ValA val) (End (Ret NI))
  Let n le1 le2 -> D $ \p ->
    let a = hash' p
        d = cons (LookupA (LI a)) (E le1) (snoc (memo a (run le1)) (Ret NI) (UpdateA (UI a)))
     in unD (cons (BindA (BI n le1 a d)) (E le2) (run le2)) p
  where
    lookup :: Ord a => a -> (a :-> Addr) -> (Addr :-> (Env,D)) -> (Env,D)
    lookup x env heap = Map.lookup x env >>= (heap Map.!?) `orElse` (Map.empty, botD)

hash' :: Trace D -> Addr
hash' p = Map.size $ snd $ materialiseState p

materialiseState :: Trace D -> (Env, Heap)
materialiseState = go Nothing (Map.empty, Map.empty) . consifyT
  where
    go :: Maybe Value -> (Env, Heap) -> Trace D -> (Env, Heap)
    go _      s             (End l)       = s
    go mb_val s@(env, heap) (ConsT l a t) = case a of
      ValA val -> go (Just val) s t
      BindA b | let !env' = Map.insert b.name b.addr env
        -> go Nothing (env', Map.insert b.addr (env',b.denot) heap) t
      LookupA a | Just (env',_d) <- Map.lookup a.addr heap -> go Nothing (env',heap) t
      App1A _   -> go Nothing s t
      UpdateA a | Just (Fun (_x,_l,env',_d)) <- mb_val -> go mb_val (env,Map.adjust (first (const env')) a.addr heap) t
        -- The d stored in the heap is still accurate as it looks for Update
        -- actions in the init trace. Theoretically, we could cough up a d based
        -- on _d from the value, though...
        --
        -- More importantly, we have to update the env', otherwise we don't
        -- sync up with the stateful semantics. E.g., if a let RHS is of the
        -- form `let a = x in λy.a`, then we have to bind the `a` in the value
        -- `λy.a`. Perhaps it would be simpler also to update the d rather than
        -- jsut mess with the env'.
      App2A a | Just (Fun (x,_l,env,_d)) <- mb_val -> go Nothing (Map.insert x a.arg env, heap) t

materialiseStates :: Trace D -> NonEmpty (Env, Heap)
materialiseStates p = materialiseState <$> prefs p
