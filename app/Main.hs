{-# OPTIONS -fplugin=MonadicBang #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Main where

import Data.Set
import Data.Set as Set
import Data.Map
import Data.Map as Map
import Control.Monad.Trans.State

type Name = String

data ExprF expr
  = Var Name
  | App expr Name
  | Lam Name expr
  | Let Name expr expr

newtype Fix f = Fix { unFix :: f (Fix f) }

type Label = Int
data Labelled f = Lab
  { at    :: !Label
  , thing :: !(f (Labelled f))
  , after :: !Label
  }

type Expr = Fix ExprF
type LExpr = Labelled ExprF

label :: Expr -> LExpr
label (Fix e) = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l,l+1))
    lab :: ExprF Expr -> State Label LExpr
    lab e = do
      at <- next
      (le, after) <- case e of
        Var n -> pure (Var n, !(next))
        App e n -> do
          le <- lab e
          pure (App le n, after le)
        Lam n e -> pure (Lam n !(lab e), !(next))
        Let n e1 e2 -> pure (Let n !(lab e1) !(lab e2), !(next))
      return Lab { at = at, thing = e', after = after }

data Action
  = AppA
  | ValA !Value
  | LetA
  | LookupA
  deriving (Eq,Ord,Show)

data Trace
  = End !Label
  | ConsT !Label !Action Trace
  | SnocT Trace !Action Label
  deriving (Eq,Ord,Show)

src, dst :: Trace -> Label

src (End l)       = l
src (ConsT l _ _) = l
src (SnocT t _ _) = src t

dst (End l)       = l
dst (SnocT _ _ l) = l
dst (ConsT _ _ t) = dst t

concatT :: Trace -> Trace -> Maybe Trace
concatT (End l) t | src t == l = Just t
                  | otherwise  = Nothing
concatT (ConsT l a t1) t2 = ConsT l a <$> concatT t1 t2)
--concatT (SnocT t1 a l) t2 | src t2 == l = concatT t1 (ConsT l a t2)

type D = Trace -> Set Trace
type (:->) = Map

data Value = Fun (D -> D)

val :: Trace -> Maybe Value
val (ValA val) = Just val
val t          = Nothing

step a l sem p = Set.map (ConsT (dst p) a) $ sem $ SnocT p a l

pref :: LExpr -> (Name :-> D) -> D
pref (Lab{ at=at, thing=e, after=after }) !env !p
  | dst p /= at = Set.empty
  | otherwise   = Set.insert (End at) $ case e of
      Var n    -> (env Map.! n) p
      App le n ->
        step AppA (at le) (pref le env) p
        `bindS` \p2 -> case val p2 of
          Just (Fun f) | Just p3 <- concatT p p2 -> f (env Map.! n) p3
          _                                      -> Set.empty
      Lam n le ->
        let val = Fun (\d -> pref le (Map.insert n d env)) in
        Set.singleton (SnocT p (ValA val) after)
      Let n le1 le2 ->
        let env' = Map.insert n (step LookupA (at le1) (pref le1 env')) env in
        step LetA (at le2) (pref le2 env') p

bindS :: Set a -> (a -> Set b) -> Set b
bindS s f = Set.unions [ f a | a <- Set.elems s ]

x,y,z :: Expr
x:y:z:_ = map (Fix . Var . (:[])) "xyz"

app :: Expr -> Name -> Expr
app e n = Fix (App e n)

lam :: Name -> Expr -> Expr
lam n e = Fix (Lam n e)

let_ :: Name -> Expr -> Expr
let_ n e1 e2 = Fix (Let n e1 e2)

e1 :: LExpr
e1 = label $ let_ "x" (lam "y" y) (app x "x")

main :: IO ()
main = print (pref e1)
