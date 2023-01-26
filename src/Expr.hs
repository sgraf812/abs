{-# LANGUAGE PatternSynonyms #-}
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
import Data.Bifunctor (first)
import qualified Text.ParserCombinators.ReadPrec as Read
import qualified Text.ParserCombinators.ReadP as ReadP
import qualified Text.Read as Read
import Data.Char

type Name = String

data ExprF expr
  = Var Name
  | App expr Name
  | Lam Name expr
  | Let Name expr expr

newtype Fix f = Fix {unFix :: f (Fix f)}

pattern FVar n = Fix (Var n)
pattern FApp e x = Fix (App e x)
pattern FLam x e = Fix (Lam x e)
pattern FLet x e1 e2 = Fix (Let x e1 e2)

type Label = Int

data Labelled f = Lab
  { at :: !Label,
    thing :: !(f (Labelled f)),
    after :: !Label
  }

type Expr = Fix ExprF

instance Eq Expr where
  e1 == e2 = go Map.empty Map.empty e1 e2
    where
      occ benv x = maybe (Left x) Right (Map.lookup x benv)
      go benv1 benv2 (Fix e1) (Fix e2) = case (e1,e2) of
        (Var x, Var y)         -> occ benv1 x == occ benv2 y
        (App f x, App g y)     -> occ benv1 x == occ benv2 y && go benv1 benv2 f g
        (Let x e1 e2, Let y e3 e4) -> go benv1' benv2' e1 e3 && go benv1' benv2' e2 e4
          where
            benv1' = Map.insert x (Map.size benv1) benv1
            benv2' = Map.insert y (Map.size benv2) benv2
        (Lam x e1', Lam y e2') -> go (Map.insert x (Map.size benv1) benv1)
                                     (Map.insert y (Map.size benv2) benv2)
                                     e1' e2'
        _                      -> False

appPrec, lamPrec :: Read.Prec
lamPrec = Read.minPrec
appPrec = lamPrec+1

-- | Example output: @F (λa. G) (H I) (λb. J b)@
instance Show Expr where
  showsPrec _ (FVar v)      = showString v
  showsPrec p (FApp f arg)  = showParen (p > appPrec) $
    showsPrec appPrec f . showString " " . showString arg
  showsPrec p (FLam b body) = showParen (p > lamPrec) $
    showString "λ" . showString b . showString "." . showsPrec lamPrec body
  showsPrec p (FLet x e1 e2) = showParen (p > lamPrec) $
    showString "let " . showString x
    . showString " = " . showsPrec lamPrec e1
    . showString " in " . showsPrec lamPrec e2

-- | The default 'ReadP.many1' function leads to ambiguity. What a terrible API.
greedyMany, greedyMany1 :: ReadP.ReadP a -> ReadP.ReadP [a]
greedyMany p  = greedyMany1 p ReadP.<++ pure []
greedyMany1 p = (:) <$> p <*> greedyMany p

-- | This monster parses Exprs in the REPL etc. It parses names that start
-- with an upper-case letter as literals and lower-case names as variables.
--
-- Accepts syntax like
-- @let x = λa. g z in (λb. j b) x@
--
-- >>> read "g z" :: Expr
-- g z
--
-- >>> read "λx.x" :: Expr
-- λx. x
--
-- >>> read "let x = x in x" :: Expr
-- let x = x in x
--
-- >>> read "let x = λa. g z in (λb. j b) x" :: Expr
-- let x = λa. g z in (λb. j b) x
--
-- >>> read "let x = λa. let y = y in a in g z" :: Expr
-- let x = λa. let y = y in a in g z
instance Read Expr where
  readPrec = Read.parens $ Read.choice
    [ FVar <$> readName
    , Read.prec appPrec $ do
        -- Urgh. Just ignore the code here as long as it works
        let spaces1 = greedyMany1 (ReadP.satisfy isSpace)
        (f:args) <- Read.readP_to_Prec $ \prec ->
          ReadP.sepBy1 (Read.readPrec_to_P Read.readPrec (prec+1)) spaces1
        guard $ not $ null args
        let to_var e = case e of FVar n -> Just n; _ -> Nothing
        Just xs <- pure $ traverse to_var args
        pure (foldl' FApp f xs)
    , Read.prec lamPrec $ do
        c <- Read.get
        guard (c `elem` "λΛ@#%\\") -- multiple short-hands for Lam
        FVar v <- Read.readPrec
        '.' <- Read.get
        FLam v <$> Read.readPrec
    , Read.prec lamPrec $ do
        Read.Ident "let" <- Read.lexP
        x <- readName
        Read.Punc "=" <- Read.lexP
        e1 <- Read.readPrec
        Read.Ident "in" <- Read.lexP
        e2 <- Read.readPrec
        pure (FLet x e1 e2)
    ]
    where
      readName = do
        Read.Ident v <- Read.lexP
        guard (not $ v `elem` ["let","in"])
        guard (all isAlphaNum v)
        pure v

type LExpr = Labelled ExprF

instance Show LExpr where
  show le = case le.thing of
    App e n -> show le.at ++ "(" ++ show e ++ " " ++ n ++ ")"
    Lam n e -> show le.at ++ "(" ++ "λ" ++ n ++ ". " ++ show e ++ ")" ++ show le.after
    Var n -> show le.at ++ "(" ++ n ++ ")"
    Let n e1 e2 -> show le.at ++ "(" ++ "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2 ++ ")"

label :: Expr -> LExpr
label (Fix e) = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l, l + 1))
    lab :: ExprF Expr -> State Label LExpr
    lab e = do
      at <- next
      (le, after) <- case e of
        Var n -> pure (Var n, -1) -- this label will never be used
        App (Fix e) n -> do
          le <- lab e
          pure (App le n, after le)
        Lam n (Fix e) -> (,) <$> (Lam n <$> lab e) <*> next
        Let n (Fix e1) (Fix e2) -> do
          le1 <- lab e1
          le2 <- lab e2
          pure (Let n le1 le2, le2.after)
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

data Value d = Fun (d -> d)

instance Show (Value d) where
  show (Fun _) = "fun"

instance Eq (Value d) where
  _ == _ = True

instance Ord (Value d) where
  compare _ _ = EQ

data Action d
  = ValA !(Value d)
  | App1A
  | App2A
  | BindA
  | LookupA !(Trace d)
  deriving (Eq, Ord)

instance Show d => Show (Action d) where
  show (ValA v) = "val(" ++ show v ++ ")"
  show (LookupA k) = "look([" ++ show (dst k) ++ "]_" ++ show (lenT k) ++ ")"
  show App1A = "app1"
  show App2A = "app2"
  show BindA = "bind"

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
dimapAction to from App1A       = App1A
dimapAction to from (ValA v)    = ValA (dimapValue to from v)
dimapAction to from App2A       = App2A
dimapAction to from BindA       = BindA
dimapAction to from (LookupA t) = LookupA (dimapTrace to from t)

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

valT :: Trace d -> Maybe (Trace d)
valT t = go (snocifyT t)
  where
    go (End _) = Nothing
    go (SnocT t a l) = case a of
      ValA _    -> Just (ConsT (dst t) a (End l))
      App1A     -> Nothing
      App2A     -> Nothing
      BindA     -> Nothing
      LookupA _ -> Nothing
    go ConsT {} = error "invalid"

val :: Trace d -> Maybe (Value d)
val t = go <$> valT t
  where
    go (ConsT _ (ValA val) _) = val

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
  _ | x == y -> e
  Var z -> Var (occ x y z)
  App e z -> App (subst x y e) (occ x y z)
  Lam z e
    | z == x -> Lam z e
    | z == y -> Lam (freshen z) (subst x y $ subst z (freshen z) e)
    | otherwise -> Lam z (subst x y e)
  Let z e1 e2
    | x == z -> Let z e1 e2
    | z == y -> Let (freshen z) (subst x y $ subst z (freshen z) e1)
                                (subst x y $ subst z (freshen z) e2)
    | otherwise -> Let z (subst x y e1) (subst x y e2)
  where
    occ x y z
      | x == z = y
      | otherwise = z
    freshen x = x ++ "'"


freshName :: Name -> Name :-> a -> Name
freshName n h = go n
  where
    go n
      | n `Map.member` h = go (n ++ "'")
      | otherwise = n

splitBalancedPrefix :: Show d => Trace d -> (Trace d, Maybe (Trace d))
splitBalancedPrefix p = -- traceIt (\(r,_)->"split" ++ "\n"  ++ show (takeT 3 p) ++ "\n" ++ show (takeT 3 r)) $
  work (consifyT p)
  where
    traceIt f res = trace (f res) res
    work p@(End _) = (p, Nothing) -- Not balanced
    work p'@(ConsT l a p) = case a of
      ValA _ -> (ConsT l a (End (src p)), Just p) -- balanced
      LookupA _ -> first (ConsT l a) (work p)
      BindA     -> first (ConsT l a) (work p)
      App1A ->
        -- we have to be extremely careful not to force mp2 too early
        let (p1, mp2) = work p
            pref = ConsT l App1A p1
            (suff, mp') = case mp2 of
              Just (ConsT l2 App2A p2) ->
                let (p3, mp4) = work p2
                 in (ConsT l2 App2A p3,mp4)
              _ -> (End (dst p1), Nothing)
         in (pref `concatT` suff,mp')
      App2A -> (p',Nothing) -- Not balanced; one closing parens too many

-- | Loop indefinitely for infinite traces!
isBalanced :: Show d => Trace d -> Bool
isBalanced p = case splitBalancedPrefix p of
  (p', Just (End l)) | l == dst p -> p' == p
  _                               -> False

data Lifted a = Lifted !a
              | Bottom
              deriving (Eq, Ord, Show)

uniqify e = evalState (go Map.empty e) 0
  where
    go benv (FLet n e1 e2) = do
      n' <- fresh
      let benv' = Map.insert n n' benv
      FLet n' <$> go benv' e1 <*> go benv' e2
    go benv (FLam n e) = do
      n' <- fresh
      let benv' = Map.insert n n' benv
      FLam n' <$> go benv' e
    go benv (FVar n) =
      pure (FVar (Map.findWithDefault n n benv))
    go benv (FApp e n) =
      FApp <$> go benv e <*> pure (Map.findWithDefault n n benv)
    fresh = state $ \k -> (idx2Name k, k+1)

    idx2Name :: Int -> Name
    idx2Name n | n <= 26   = [chr (ord 'a' + n)]
               | otherwise = "t" ++ show n
