{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans.State
import Debug.Trace
import Data.Maybe
import Data.Foldable
import Data.Ord

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
        Var n -> (,) (Var n) <$> next
        App (Fix e) n -> do
          le <- lab e
          pure (App le n, after le)
        Lam n (Fix e) -> (,) <$> (Lam n <$> lab e) <*> next
        Let n (Fix e1) (Fix e2) -> do
          le <- Let n <$> lab e1 <*> lab e2
          after <- next
          pure (le, after)
      pure Lab { at = at, thing = le, after = after }

data Action
  = AppA
  | ValA !Value
  | BetaA
  | LetA
  | LookupA
  deriving (Eq,Ord,Show)

data Trace
  = End !Label
  | ConsT !Label !Action Trace
  | SnocT Trace !Action Label
  deriving (Eq,Ord)

instance Show Trace where
  show (End l) = show l
  show (ConsT l a t) = show l ++ "-" ++ show a ++ "->" ++ show t
  show (SnocT t a l) = show t ++ "-" ++ show a ++ "->" ++ show l

instance Show LExpr where
  show le = case le.thing of
    App e n -> show le.at ++ "(" ++ show e ++ "@" ++ n ++ ")"
    Lam n e -> show le.at ++ "(" ++ "λ" ++ n ++ ". " ++ show e ++ ")" ++ show le.after
    Var n -> show le.at ++ "(" ++ n ++ ")" ++ show le.after
    Let n e1 e2 -> show le.at ++ "(" ++ "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2 ++ ")" ++ show le.after

src, dst :: Trace -> Label

src (End l)       = l
src (ConsT l _ _) = l
src (SnocT t _ _) = src t

dst (End l)       = l
dst (SnocT _ _ l) = l
dst (ConsT _ _ t) = dst t

consifyT :: Trace -> Trace
consifyT t = go End t
  where
    go f (End l)       = f l
    go f (ConsT l a t) = ConsT l a (go f t)
    go f (SnocT t a l) = go (\l' -> ConsT l' a (f l)) t

snocifyT :: Trace -> Trace
snocifyT t = go End t
  where
    go f (End l)       = f l
    go f (SnocT t a l) = SnocT (go f t) a l
    go f (ConsT l a t) = go (\l' -> SnocT (f l) a l') t

concatT :: Trace -> Trace -> Maybe Trace
concatT t1 t2 | dst t1 /= src t2 = Nothing
              | otherwise        = Just (con t1 t2)
  where
    con (End _)        t2 = t2
    con (SnocT t1 a l) t2 = con t1 (ConsT (dst t1) a t2)
    con (ConsT l a t1) t2 = ConsT l a (con t1 t2)

lenT :: Trace -> Int
lenT (End _) = 0
lenT (ConsT _ _ t) = 1 + lenT t
lenT (SnocT t _ _) = 1 + lenT t

type D = Trace -> Set Trace
type (:->) = Map

data Value = Fun (D -> D)

instance Eq Value where
  _ == _ = True

instance Ord Value where
  compare _ _ = EQ

instance Show Value where
  show (Fun _) = "Fun"

val :: Trace -> Maybe Value
val t = go (snocifyT t)
  where
    go (End _) = Nothing
    go (SnocT t a l) | ValA val <- a = Just val
                     | otherwise     = go t
    go ConsT{} = error "invalid"

enter :: Action -> Label -> D -> D
enter a l sem p = Set.map (ConsT (dst p) a) $ sem $ SnocT p a l

pref, pref' :: LExpr -> (Name :-> D) -> D

pref le env p =
  let res = pref' le env p in
  if any (\p' -> dst p /= src p') res then error (show le ++ " " ++ show p ++ " " ++ show res) else
  res

pref' (Lab{ at=at, thing=e, after=after }) !env !p
  | dst p /= at = Set.empty
  | otherwise   = Set.insert (End at) $ case e of
      Var n    -> (env Map.! n) p
      App le n ->
        enter AppA le.at (pref le env) p
        `bindS` \p2 -> case concatT p p2 of
          Just p3 -> Set.insert p2 $ case val p2 of
            Just (Fun f) -> Set.map (fromJust . concatT p2) $ f (env Map.! n) p3
            _            -> Set.empty
      Lam n le ->
        let val = Fun (\d -> enter BetaA (le.at) (pref le (Map.insert n d env)) . traceShowId) in
        --traceShow p $
        --traceShow at $
        --traceShow after $
        --traceShowId $
        Set.singleton (ConsT at (ValA val) (End after))
      Let n le1 le2 ->
        let env' = Map.insert n (enter LookupA le1.at (pref le1 env')) env in
        enter LetA le2.at (pref le2 env') p
        `bindS` \p -> Set.insert p $ if dst p /= le2.after then Set.empty else Set.singleton (SnocT p LetA after)

bindS :: Ord b => Set a -> (a -> Set b) -> Set b
bindS s f = Set.unions [ f a | a <- Set.elems s ]

x,y,z :: Expr
x:y:z:_ = map (Fix . Var . (:[])) "xyz"

app :: Expr -> Name -> Expr
app e n = Fix (App e n)

lam :: Name -> Expr -> Expr
lam n e = Fix (Lam n e)

let_ :: Name -> Expr -> Expr -> Expr
let_ n e1 e2 = Fix (Let n e1 e2)

e1 :: LExpr
e1 = label $ lam "y" y

e2 :: LExpr
e2 = label $ let_ "x" (lam "y" y) (app (app x "x") "x")

pickMax :: Set Trace -> Maybe Trace
pickMax s | null s    = Nothing
          | otherwise = Just $ maximumBy (comparing lenT) (Set.elems s)

main :: IO ()
main = do
  print e2
  print (pref e1 Map.empty (End (at e1)))
  print (pickMax $ pref e2 Map.empty (End (at e2)))
