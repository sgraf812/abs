{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main (main) where

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
        Var n -> (,) (Var n) <$> next
        App (Fix e) n -> do
          le <- lab e
          pure (App le n, after le)
        Lam n (Fix e) -> (,) <$> (Lam n <$> lab e) <*> next
        Let n (Fix e1) (Fix e2) -> do
          le2 <- lab e2
          le <- Let n <$> lab e1 <*> pure le2
          pure (le, le2.after)
      pure Lab {at = at, thing = le, after = after}

data Action
  = AppA !Name
  | ValA !Value
  | BetaA !Name
  | BindA !Name !Label !D
  | LookupA
  deriving (Eq, Ord, Show)

data Trace
  = End !Label
  | ConsT !Label !Action Trace
  | SnocT Trace !Action Label
  deriving (Eq, Ord)

-- think of type Trace = Nu TraceF; e.g., greatest fixed-point, to allow
-- infinite traces Haskell data types are greatest fixed-points

instance Show Trace where
  show (End l) = "[" ++ show l ++ "]"
  show (ConsT l a t) = "[" ++ show l ++ "]-" ++ show a ++ "->" ++ show t ++ ""
  show (SnocT t a l) = show t ++ "-" ++ show a ++ "->[" ++ show l ++ "]"

instance Show LExpr where
  show le = case le.thing of
    App e n -> show le.at ++ "(" ++ show e ++ "@" ++ n ++ ")"
    Lam n e -> show le.at ++ "(" ++ "λ" ++ n ++ ". " ++ show e ++ ")" ++ show le.after
    Var n -> show le.at ++ "(" ++ n ++ ")" ++ show le.after
    Let n e1 e2 -> show le.at ++ "(" ++ "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2 ++ ")" ++ show le.after

src, dst :: Trace -> Label
src (End l) = l
src (ConsT l _ _) = l
src (SnocT t _ _) = src t
dst (End l) = l
dst (SnocT _ _ l) = l
dst (ConsT _ _ t) = dst t

consifyT :: Trace -> Trace
consifyT t = go End t
  where
    go f (End l) = f l
    go f (ConsT l a t) = ConsT l a (go f t)
    go f (SnocT t a l) = go (\l' -> ConsT l' a (f l)) t

snocifyT :: Trace -> Trace
snocifyT t = go End t
  where
    go f (End l) = f l
    go f (SnocT t a l) = SnocT (go f t) a l
    go f (ConsT l a t) = go (\l' -> SnocT (f l) a l') t

concatT :: Trace -> Trace -> Trace
concatT t1 t2 = con t1 t2
  where
    con :: Trace -> Trace -> Trace
    con (End l) t2 = assert (l == src t2) t2
    con (SnocT t1 a l) t2 = con t1 (assert (l == src t2) (ConsT (dst t1) a t2))
    con (ConsT l a t1) t2 = ConsT l a (con t1 t2)
    assert b e = if b then e else undefined

takeT :: Int -> Trace -> Trace
takeT n t = go n (consifyT t)
  where
    go 0 (ConsT l _ _) = End l
    go _ (End l) = End l
    go n (ConsT l a t) = ConsT l a (takeT (n - 1) t)
    go _ SnocT {} = error "impossible"

lenT :: Trace -> Int
lenT (End _) = 0
lenT (ConsT _ _ t) = 1 + lenT t
lenT (SnocT t _ _) = 1 + lenT t

type D = Trace -> Trace

type (:->) = Map

instance Eq D where
  _ == _ = True

instance Ord D where
  compare _ _ = EQ

instance Show D where
  show _ = "D"

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
    go (SnocT t a l)
      | ValA val <- a = Just val
      | otherwise = go t
    go ConsT {} = error "invalid"

step :: Action -> Label -> D -> D
step a l sem p = ConsT (dst p) a $ sem $ SnocT p a l

maxinf, maxinf' :: LExpr -> (Name :-> D) -> D
maxinf le env p =
  let res = maxinf' le env p
   in -- if dst p /= src res then error (show le ++ " " ++ show p ++ " " ++ show res) else
      res
maxinf' (Lab {at = at, thing = e, after = after}) !env !p
  | dst p /= at = End at -- stuck. only happens on the initial call, I guess??? In all other cases we go through the step function
  | otherwise = case e of
      Var n -> (env Map.! n) p
      App le n ->
        let p2 = step (AppA n) le.at (maxinf le env) p
         in concatT p2 $ case val p2 of
              Just (Fun f) -> f (env Map.! n) (concatT p p2)
              Nothing -> End (dst p2)
      Lam n le ->
        let val = Fun (\d -> step (BetaA n) (le.at) (maxinf le (Map.insert n d env)))
         in -- traceShow p $
            -- traceShow at $
            -- traceShow after $
            -- traceShowId $
            ConsT at (ValA val) (End after)
      Let n le1 le2 ->
        let d = step LookupA le1.at (maxinf le1 env')
            env' = Map.insert n d env
         in step (BindA n le1.at d) le2.at (maxinf le2 env') p

bindS :: Ord b => Set a -> (a -> Set b) -> Set b
bindS s f = Set.unions [f a | a <- Set.elems s]

x, y, z :: Expr
x : y : z : _ = map (Fix . Var . (: [])) "xyz"

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

ew :: LExpr
ew = label $ let_ "y" (lam "x" (app x "x")) (app y "y")

pickMax :: Set Trace -> Maybe Trace
pickMax s
  | null s = Nothing
  | otherwise = Just $ maximumBy (comparing lenT) (Set.elems s)

unlabel :: LExpr -> Expr
unlabel le = Fix $ case le.thing of
  Var n -> Var n
  Lam x e -> Lam x $ unlabel e
  App e x -> App (unlabel e) x
  Let x e1 e2 -> Let x (unlabel e1) (unlabel e2)

type Configuration = (Heap, Expr, Stack)

type Heap = Name :-> Expr

type Stack = [Frame]

data Frame = Apply Name

instance Show Frame where
  show (Apply x) = "$" ++ x

instance Show Expr where
  show e = case unFix e of
    App e n -> show e ++ "@" ++ n
    Lam n e -> "(" ++ "λ" ++ n ++ "." ++ show e ++ ")"
    Var n -> n
    Let n e1 e2 -> "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2

instance {-# OVERLAPPING #-} Show Heap where
  showsPrec _ h = showListWith (\(x, e) -> ((x ++ "↦" ++ show e) ++)) $ Map.assocs h

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

freshName :: Name -> Map Name a -> Name
freshName n h = go n
  where
    go n
      | n `Map.member` h = go (n ++ "'")
      | otherwise = n

smallStep :: Expr -> [Configuration]
smallStep e = go (Map.empty, e, [])
  where
    go :: Configuration -> [Configuration]
    go c@(h, Fix e, s) =
      c : case (e, s) of
        (Var n, _) -> go (h, h Map.! n, s)
        (App e x, _) -> go (h, e, Apply x : s)
        (Lam x e, []) -> []
        (Lam x e, Apply y : s') -> go (h, subst x y e, s')
        (Let x e1 e2, _) ->
          let x' = freshName x h
           in go (Map.insert x' (subst x x' e1) h, (subst x x' e2), s)

indexAtE :: Label -> LExpr -> Expr
indexAtE l e = fromJust (find e)
  where
    find le@(Lab {at = at, thing = e}) | at == l = Just (unlabel le)
    find le = case le.thing of
      Var _ -> Nothing
      App e _ -> find e
      Lam _ e -> find e
      Let _ e1 e2 -> find e1 <|> find e2

tracesAt :: Label -> Trace -> [Trace]
tracesAt l t = case t of
  End l' -> [t | l == l']
  ConsT l' a t' -> [End l' | l == l'] ++ map (ConsT l' a) (tracesAt l t')
  SnocT t' a l' -> tracesAt l t' ++ [SnocT t' a l' | l' == l]

-- post(maxinf le []) will be the reachability semantics, e.g., small-step!
-- Wart: Instead of a (set of) Trace `t`, it should take a (set of) Configuration `c`
-- such that `config p = c` (that is, we don't know how to efficiently compute
-- the concretisation function γ(cs) = ts). By doing it this way, we can
-- actually compute.
-- The lifting to sets (of initialisation Traces/Configurations) is routine.
-- we return a list instead of a set, because it might be infinite and we want to
-- enumerate.
--
-- Note that we never look at the `Expr` returned by the indexing function.
post :: LExpr -> D -> Trace -> Label -> [Configuration]
post le d p l = map (config (unlabel le) . concatT p) (tracesAt l (d p))

config :: Expr -> Trace -> Configuration
config e p = go (snocifyT p)
  where
    go :: Trace -> Configuration
    go ConsT {} = undefined
    go (End l) = (Map.empty, e, [])
    go (SnocT t a l) =
      let c@(h,Fix e,s) = go t in
      case a of
        BindA _ _ _  | Let n e1 e2 <- e ->
          let n' = freshName n h
              e1' = subst n n' e1
              e2' = subst n n' e2
           in (Map.insert n' e1' h, e2', s)
        AppA _       | App e n <- e -> (h, e, Apply n:s)
        ValA (Fun _) | Lam _ _ <- e -> c
        BetaA _      | (Apply n':s') <- s, Lam n eb <- e -> (h, subst n n' eb, s')
        LookupA      | Var n <- e -> (h, h Map.! n, s)
        _ -> error (show a)

defnSmallStep :: Expr -> [Configuration]
defnSmallStep e = map (config e) (prefs sem)
  where
    le = label e
    sem = maxinf le Map.empty (End (le.at))

-- | Turns a maximal finite or infinite trace into the list of its prefix
-- traces. The list is finite iff the incoming trace is.
prefs :: Trace -> [Trace]
prefs t = go (consifyT t)
  where
    go t = case t of
      End l -> [t]
      ConsT l a t' -> End l : map (ConsT l a) (prefs t')
      SnocT{} -> undefined

-- |
-- >>> e2
-- 1(let x = 2(λy. 3(y)4)5 in 6(7(8(x)9@x)@x))10
--
-- >>> takeT 20 $ maxinf e2 Map.empty (End (at e2))
-- [1]-LeaveLetA->[6]-AppA->[7]-AppA->[8]-LookupA->[2]-ValA Fun->[5]-BetaA->[3]-LookupA->[2]-ValA Fun->[5]-BetaA->[3]-LookupA->[2]-ValA Fun->[5]-BindA "x" D->[10]
main :: IO ()
main = forM_ [e1, e2, ew] $ \e -> do
  putStrLn "----------------"
  print e
  putStrLn "maximal and infinite trace"
  print $ takeT 20 $ maxinf e Map.empty (End (at e))
  putStrLn "smallStep"
  mapM_ print $ take 20 $ smallStep (unlabel e)
  putStrLn "tracesAt 2"
  mapM_ print $ tracesAt 2 $ takeT 20 $ maxinf e Map.empty (End (at e))
  putStrLn "defnSmallStep"
  mapM_ print $ take 20 $ defnSmallStep (unlabel e)
