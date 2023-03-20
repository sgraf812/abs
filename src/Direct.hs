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

module Direct (D(..), Value(..), maxinf, maxinfD) where

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
import GHC.Stack

orElse = flip fromMaybe

type instance AddrOrD D = D
data instance Value D = Fun (D -> D)

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

whenAtP :: Label -> D -> D
whenAtP l d = askP $ \p -> if l == dst p then d else botD

step :: Action D -> Label -> D
step a l = D $ \p -> ConsT (dst p) a (End l)

memo :: Addr -> Label -> D -> D
memo a l sem = askP $ \pi ->
  let (l', d) = case update a (snocifyT pi) of
        Just (l', v) -> (l', step (ValA v) returnLabel)
        Nothing      -> (l, sem)
      update addr (SnocT pi' a _)
        | UpdateA addr' <- a
        , addr == addr'
        = valT pi'
        | otherwise
        = update addr pi'
      update _ End{} = Nothing
  in step (LookupA a) l' >.> d >.> whenAtP returnLabel (step (UpdateA a) returnLabel)

maxinfD :: LExpr -> (Name :-> D) -> D
maxinfD le env = go le env
  where
    (!⊥) :: Ord a => (a :-> D) -> a -> D
    env !⊥ x = Map.findWithDefault botD x env
    go :: LExpr -> (Name :-> D) -> D
    go le !env = whenAtP le.at $ case le.thing of
      Var n -> env !⊥ n
      App le n -> whenP (Map.lookup n env) $ \d ->
        let apply = askP $ \p -> whenP (val p) $ \(Fun f) -> f d
         in step App1A le.at >.> go le env >.> apply
      Lam n le' ->
        let val = Fun (\d -> step (App2A n d) le'.at >.> go le' (Map.insert n d env))
         in step (ValA val) returnLabel
      Let n le1 le2 -> askP $ \p ->
        let a = hash p
            d = memo a le1.at (go le1 env')
            env' = Map.insert n d env
         in step (BindA n a d) le2.at >.> go le2 env'

maxinf :: LExpr -> (Name :-> D) -> Trace D -> Trace D
maxinf le env p = unD (maxinfD le env) p

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
