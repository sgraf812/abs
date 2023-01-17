{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Expr where

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
import Text.Show (showListWith)
import Debug.Trace

type Name = String

data ExprF expr
  = Var Name
  | App expr Name
  | Lam Name expr
  | Let Name expr expr

newtype Fix f = Fix {unFix :: f (Fix f)}

type Label = Int

data Labelled f = Lab
  { at :: !Label,
    thing :: !(f (Labelled f)),
    after :: !Label
  }

type Expr = Fix ExprF

type LExpr = Labelled ExprF

label :: Expr -> LExpr
label (Fix e) = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l, l + 1))
    lab :: ExprF Expr -> State Label LExpr
    lab e = do
      at <- next
      (le, after) <- case e of
        Var n -> (,) (Var n) <$> next -- this label will never be used
        App (Fix e) n -> do
          le <- lab e
          pure (App le n, after le)
        Lam n (Fix e) -> (,) <$> (Lam n <$> lab e) <*> next
        Let n (Fix e1) (Fix e2) -> do
          le2 <- lab e2
          le <- Let n <$> lab e1 <*> pure le2
          pure (le, le2.after)
      pure Lab {at = at, thing = le, after = after}

unlabel :: LExpr -> Expr
unlabel le = Fix $ case le.thing of
  Var n -> Var n
  Lam x e -> Lam x $ unlabel e
  App e x -> App (unlabel e) x
  Let x e1 e2 -> Let x (unlabel e1) (unlabel e2)

indexAtE :: Label -> LExpr -> Expr
indexAtE l e = unlabel $ indexAtLE l e

indexAtLE :: Label -> LExpr -> LExpr
indexAtLE l e = fromMaybe (error (show l ++ " " ++ show e)) (find e)
  where
    find le@(Lab {at = at, thing = e}) | at == l = Just le
    find le = case le.thing of
      Var _ -> Nothing
      App e _ -> find e
      Lam _ e -> find e
      Let _ e1 e2 -> find e1 <|> find e2

atToAfter :: LExpr -> Label -> Label
atToAfter e at = (indexAtLE at e).after

data Action d
  = AppA
  | ValA !(Value d)
  | BetaA
  | BindA
  | EnterA
  deriving (Eq, Ord, Show)

data Value d = Fun (d -> d)

data Trace d
  = End !Label
  | ConsT !Label !(Action d) (Trace d)
  | SnocT (Trace d) !(Action d) Label
  deriving (Eq, Ord)

-- think of type Trace = Nu TraceF; e.g., greatest fixed-point, to allow
-- infinite traces Haskell data types are greatest fixed-points

instance Show d => Show (Trace d) where
  show (End l) = "[" ++ show l ++ "]"
  show (ConsT l a t) = "[" ++ show l ++ "]-" ++ show a ++ "->" ++ show t ++ ""
  show (SnocT t a l) = show t ++ "-" ++ show a ++ "->[" ++ show l ++ "]"

instance Show Expr where
  show e = case unFix e of
    App e n -> show e ++ "@" ++ n
    Lam n e -> "(" ++ "λ" ++ n ++ "." ++ show e ++ ")"
    Var n -> n
    Let n e1 e2 -> "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2

instance Show LExpr where
  show le = case le.thing of
    App e n -> show le.at ++ "(" ++ show e ++ "@" ++ n ++ ")"
    Lam n e -> show le.at ++ "(" ++ "λ" ++ n ++ ". " ++ show e ++ ")" ++ show le.after
    Var n -> show le.at ++ "(" ++ n ++ ")"
    Let n e1 e2 -> show le.at ++ "(" ++ "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2 ++ ")"

src, dst :: Trace d -> Label
src (End l) = l
src (ConsT l _ _) = l
src (SnocT t _ _) = src t
dst (End l) = l
dst (SnocT _ _ l) = l
dst (ConsT _ _ t) = dst t

dimapTrace :: (d1 -> d2) -> (d2 -> d1) -> Trace d1 -> Trace d2
dimapTrace to from (End l) = End l
dimapTrace to from (ConsT l a t) = ConsT l (dimapAction to from a) (dimapTrace to from t)
dimapTrace to from (SnocT t a l) = SnocT (dimapTrace to from t) (dimapAction to from a) l

dimapAction :: (d1 -> d2) -> (d2 -> d1) -> Action d1 -> Action d2
dimapAction to from AppA     = AppA
dimapAction to from (ValA v) = ValA (dimapValue to from v)
dimapAction to from BetaA    = BetaA
dimapAction to from BindA    = BindA
dimapAction to from EnterA   = EnterA

dimapValue :: (d1 -> d2) -> (d2 -> d1) -> Value d1 -> Value d2
dimapValue to from (Fun f) = Fun (to . f . from)

consifyT :: Trace d -> Trace d
consifyT t = go End t
  where
    go f (End l) = f l
    go f (ConsT l a t) = ConsT l a (go f t)
    go f (SnocT t a l) = go (\l' -> ConsT l' a (f l)) t

snocifyT :: Trace d -> Trace d
snocifyT t = go End t
  where
    go f (End l) = f l
    go f (SnocT t a l) = SnocT (go f t) a l
    go f (ConsT l a t) = go (\l' -> SnocT (f l) a l') t

concatT :: Trace d -> Trace d -> Trace d
concatT t1 t2 = con t1 t2
  where
    con :: Trace d -> Trace d -> Trace d
    con (End l) t2 = assert (l == src t2) t2
    con (SnocT t1 a l) t2 = con t1 (assert (l == src t2) (ConsT (dst t1) a t2))
    con (ConsT l a t1) t2 = ConsT l a (con t1 t2)
    assert b e = if b then e else undefined

takeT :: Int -> Trace d -> Trace d
takeT n t = go n (consifyT t)
  where
    go 0 (ConsT l _ _) = End l
    go _ (End l) = End l
    go n (ConsT l a t) = ConsT l a (takeT (n - 1) t)
    go _ SnocT {} = error "impossible"

dropT :: Int -> Trace d -> Trace d
dropT 0 t = t
dropT n t = go n (consifyT t)
  where
    go 0 t = t
    go _ (End l) = End l
    go n (ConsT _ _ t) = dropT (n - 1) t
    go _ SnocT{} = error "impossible"

lenT :: Trace d -> Int
lenT (End _) = 0
lenT (ConsT _ _ t) = 1 + lenT t
lenT (SnocT t _ _) = 1 + lenT t

instance Eq (Value d) where
  _ == _ = True

instance Ord (Value d) where
  compare _ _ = EQ

instance Show (Value d) where
  show (Fun _) = "Fun"

val :: Trace d -> Maybe (Value d)
val t = go (snocifyT t)
  where
    go (End _) = Nothing
    go (SnocT t a l) = case a of
      ValA val -> Just val
      AppA     -> Nothing
      BetaA    -> Nothing
      BindA    -> Nothing
      EnterA   -> Nothing
      --UpdateA -> go t -- call-by-need update frames are transparent!
    go ConsT {} = error "invalid"

type (:->) = Map

tracesAt :: Label -> Trace d -> [Trace d]
tracesAt l t = case t of
  End l' -> [t | l == l']
  ConsT l' a t' -> [End l' | l == l'] ++ map (ConsT l' a) (tracesAt l t')
  SnocT t' a l' -> tracesAt l t' ++ [SnocT t' a l' | l' == l]

-- | Turns a maximal finite or infinite trace into the list of its prefix
-- traces. The list is finite iff the incoming trace is.
prefs :: Trace d -> [Trace d]
prefs t = go (consifyT t)
  where
    go t = case t of
      End l -> [t]
      ConsT l a t' -> End l : map (ConsT l a) (go t')
      SnocT{} -> undefined

subst :: Name -> Name -> Expr -> Expr
subst x y (Fix e) = Fix $ case e of
  Var z -> Var (occ x y z)
  App e z -> App (subst x y e) (occ x y z)
  Lam z e
    | z == x -> Lam z e
    | z == y -> undefined
    | otherwise -> Lam z (subst x y e)
  Let z e1 e2
    | x == z -> Let z e1 e2
    | z == y -> undefined
    | otherwise -> Let z (subst x y e1) (subst x y e2)
  where
    occ x y z
      | x == z = y
      | otherwise = z

freshName :: Name -> Name :-> a -> Name
freshName n h = go n
  where
    go n
      | n `Map.member` h = go (n ++ "'")
      | otherwise = n

data Frame = Apply Name deriving Eq

instance Show Frame where
  show (Apply x) = "$" ++ x

data ActionBalance
  = Open !Frame
  | Close !Frame
  | Tail -- "tail call"
  | Balanced
  deriving (Eq, Show)

matchActionBalance :: Action d -> ActionBalance
matchActionBalance ValA{}   = Balanced
matchActionBalance AppA{}   = Open  (Apply "")
matchActionBalance BetaA{}  = Close (Apply "")
matchActionBalance BindA{}  = Tail
matchActionBalance EnterA{} = Tail

sameActionKind :: Action d -> Action d -> Bool
sameActionKind ValA{}   ValA{}   = True
sameActionKind AppA{}   AppA{}   = True
sameActionKind BetaA{}  BetaA{}  = True
sameActionKind BindA{}  BindA{}  = True
sameActionKind EnterA{} EnterA{} = True
sameActionKind _        _        = False

splitBalancedExecution :: Show d => (Label -> Label) -> Trace d -> Maybe (Trace d, Trace d)
splitBalancedExecution end p = open [] (End (src p)) (consifyT p)
  where
    shift acc (ConsT l a t) k = k (SnocT acc a (src t)) t
    shift acc (End l)       k = k acc (End l)
    open fs acc (End _) = Nothing -- No transition => no opening => No balanced execution! NB: Values are Balanced and do a ValA transition
    open fs acc t@(ConsT l a t') = case matchActionBalance a of
      Open f'  -> shift acc t (go (f':fs)) -- Found an Open. Just balancing the stack from hereon, the job of go.
      Balanced -> shift acc t (go fs)      -- Balanced is like Open followed by Close
      Close _  -> Nothing                  -- Need an Open first! => Unbalanced
      Tail     -> shift acc t (open fs)    -- No effect on balance (unlike Balanced). Still looking for Open, hence recurse with open
    go [] acc t = Just (acc, t) -- done
    go (f:fs) acc t = case t of
      End _ -> Nothing
      ConsT _ a' t' -> case matchActionBalance a' of
        Open f'                 -> shift acc t (go (f':f:fs)) -- push
        Close f'
          | f == f'             -> shift acc t (go fs)        -- pop
          | otherwise           -> Nothing                    -- unbalanced/stuck. Should not happen for any trace generated by the semantics, so perhaps undefined?
        Tail                    -> shift acc t (go (f:fs))    -- just shift
        Balanced                -> shift acc t (go (f:fs))    -- just shift, too: It's fs if we first pushed an then popped
