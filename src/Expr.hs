{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}

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
import GHC.Stack
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Kind

assert :: HasCallStack => Bool -> a -> a
assert True  x = x
assert False _ = error "assertion failure"

assertMsg :: HasCallStack => Bool -> String -> a -> a
assertMsg True  _   x = x
assertMsg False msg _ = error ("assertion failure: " ++ msg)

type Name = String

data ExprF expr
  = Var Name
  | App expr Name
  | Lam Name expr
  | Let Name expr expr

newtype Fix f = Fix {unFix :: f (Fix f)}
type Expr = Fix ExprF
pattern FVar n = Fix (Var n)
pattern FApp e x = Fix (App e x)
pattern FLam x e = Fix (Lam x e)
pattern FLet x e1 e2 = Fix (Let x e1 e2)

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

type Label = Int

returnLabel :: Label
returnLabel = 0

data Labelled f = Lab
  { at :: !Label
  , thing :: !(f (Labelled f))
  }

instance Eq (Labelled f) where
  l1 == l2 = l1.at == l2.at

type LExpr = Labelled ExprF
pattern LVar n <- (thing -> Var n)
pattern LApp e x <- (thing -> App e x)
pattern LLam x e <- (thing -> Lam x e)
pattern LLet x e1 e2 <- (thing -> Let x e1 e2)

instance Show LExpr where
  show le = show le.at ++ parens (case le.thing of
    App e n -> show e ++ " " ++ n
    Lam n e -> "λ" ++ n ++ ". " ++ show e
    Var n -> n
    Let n e1 e2 -> "let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2)
    where
      parens s = "(" ++ s ++ ")"

showLabel :: ProgPoint d -> String
showLabel (Ret _) = "[↵]"
showLabel (E e) = "[" ++ show e.at ++ "]"

instance Show (RetX d) => Show (ProgPoint d) where
  show (Ret v) = "↵" ++ show v
  show (E e) = show e.at

instance Eq (ProgPoint d) where
  Ret _ == Ret _ = True
  E e1 == E e2 = e1.at == e2.at
  _ == _ = False

label :: Expr -> LExpr
label (Fix e) = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l, l + 1))
    lab :: ExprF Expr -> State Label LExpr
    lab e = do
      at <- next
      le <- case e of
        Var n -> pure (Var n)
        App (Fix e) n -> do
          le <- lab e
          pure (App le n)
        Lam n (Fix e) -> Lam n <$> lab e
        Let n (Fix e1) (Fix e2) -> do
          le1 <- lab e1
          le2 <- lab e2
          pure (Let n le1 le2)
      pure Lab {at = at, thing = le}

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

eqPoint :: ProgPoint v -> ProgPoint v -> Bool
eqPoint (Ret _) (Ret _) = True
eqPoint (E e1)  (E e2)  = e1.at == e2.at
eqPoint _       _       = False

type Val = LExpr

data ProgPoint d = Ret !(RetX d) | E !LExpr

isRet :: ProgPoint d -> Bool
isRet (Ret _) = True
isRet _       = False

mapProgPoint :: (RetX d1 -> RetX d2) -> ProgPoint d1 -> ProgPoint d2
mapProgPoint f (Ret d1) = Ret (f d1)
mapProgPoint _ (E e) = E e

pattern DVar n <- (E (LVar n))
pattern DApp e x <- (E (LApp e x))
pattern DLam x e <- (E (LLam x e))
pattern DLet x e1 e2 <- (E (LLet x e1 e2))

isVal :: LExpr -> Bool
isVal LLam{} = True
isVal _      = False

type Addr = Int

-- | Must be injective in the trace; but for conformance to the stateful
-- semantics, we'll return the number of bind actions in the trace
alloc :: Trace d -> Addr
alloc (End l) = 0
alloc (ConsT _ (BindA _) p) = alloc p + 1
alloc (ConsT _ _         p) = alloc p
alloc (SnocT p (BindA _) _) = alloc p + 1
alloc (SnocT p _         _) = alloc p

class HasLabel s where
  labelOf :: s -> Label

instance HasLabel (Labelled l) where
  labelOf l = l.at

instance HasLabel (ProgPoint d) where
  labelOf (Ret _) = returnLabel
  labelOf (E e)   = e.at

type family StateX d
type family RetX d
type family ValX d
type family EnvRng d

data NoInfo = NI deriving Eq
instance Show NoInfo where show _ = ""

data BindInfo d = BI { name :: !Name, rhs :: !LExpr, addr :: !Addr, denot :: !d }
instance Eq (BindInfo d) where bi1 == bi2 = bi1.name == bi2.name && bi1.addr == bi2.addr
instance Show (BindInfo d) where show bi = "(" ++ bi.name ++ "↦" ++ show bi.addr ++ ")"

data LookupInfo = LI { addr :: !Addr } deriving Eq
instance Show LookupInfo where show li = "(" ++ show li.addr ++ ")"

data UpdateInfo = UI { addr :: !Addr } deriving Eq
instance Show UpdateInfo where show ui = "(" ++ show ui.addr ++ ")"

data App1Info d = A1I { arg1 :: !(EnvRng d) }
instance Eq (App1Info d) where ai1 == ai2 = True
instance Show (App1Info d) where show ai = ""

data App2Info d = A2I { name :: !Name, arg :: !(EnvRng d) }
instance Eq (App2Info d) where ai1 == ai2 = ai1.name == ai2.name
instance Show (App2Info d) where show ai = "(" ++ ai.name ++ ")"

data Action d
  = ValA !(ValX d)
  | App1A !(App1Info d)
  | App2A !(App2Info d)
  | BindA !(BindInfo d)
  | LookupA !LookupInfo
  | UpdateA !UpdateInfo

deriving instance Eq (ValX d) => Eq (Action d)

instance Show (ValX d) => Show (Action d) where
  show a = case a of
    ValA x -> "val" ++ show x
    LookupA x -> "look" ++ show x
    UpdateA x -> "upd" ++ show x
    App1A x -> "app1" ++ show x
    App2A x -> "app2" ++ show x
    BindA x -> "bind" ++ show x

data Trace d
  = End !(StateX d)
  | ConsT !(StateX d) !(Action d) (Trace d)
  | SnocT (Trace d) !(Action d) !(StateX d)

deriving instance (Eq (ValX d), Eq (StateX d)) => Eq (Trace d)

-- think of type Trace = Nu TraceF; e.g., greatest fixed-point, to allow
-- infinite traces Haskell data types are greatest fixed-points

instance (Show (Action d), Show (StateX d)) => Show (Trace d) where
  show (End l) = show l
  show (ConsT l a t) = show l ++ "-" ++ show a ++ "->" ++ show t ++ ""
  show (SnocT t a l) = show t ++ "-" ++ show a ++ "->" ++ show l

sameLabelsInTrace :: (HasLabel (StateX d1), HasLabel (StateX d2)) => Trace d1 -> Trace d2 -> Bool
sameLabelsInTrace t1 t2 = traceLabels t1 == traceLabels t2

src, tgt :: Trace d -> StateX d
src (End l) = l
src (ConsT l _ _) = l
src (SnocT t _ _) = src t
tgt (End l) = l
tgt (SnocT _ _ l) = l
tgt (ConsT _ _ t) = tgt t

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

concatT :: (HasCallStack, HasLabel (StateX d)) => Trace d -> Trace d -> Trace d
concatT t1 t2 = con t1 t2
  where
    con (End l) t2 = assert (labelOf l == labelOf (src t2)) t2
    con (SnocT t1 a l) t2 = con t1 (ConsT (tgt t1) a (assert (labelOf l == labelOf (src t2)) t2))
    con (ConsT l a t1) t2 = ConsT l a (con t1 t2)

takeT :: Int -> Trace d -> Trace d
takeT n t = go n t
  where
    go 0 (ConsT l _ _) = End l
    go _ (End l) = End l
    go n (ConsT l a t) = ConsT l a (takeT (n - 1) t)
    go n t@SnocT{} = go n (consifyT t)

dropT :: Int -> Trace d -> Trace d
dropT 0 t = t
dropT n t = go n t
  where
    go 0 t = t
    go _ (End l) = End l
    go n (ConsT _ _ t) = dropT (n - 1) t
    go n t@SnocT{} = go n (consifyT t)

lenT :: Trace d -> Int
lenT (End _) = 0
lenT (ConsT _ _ t) = 1 + lenT t
lenT (SnocT t _ _) = 1 + lenT t

-- |
-- prop> splitsT t = [ (dropT n t, takeT n t) | n <- [0..lenT t] ]
splitsT :: Trace d -> NonEmpty (Trace d, Trace d)
splitsT t = go (takeT 0 t') t'
  where
    t' = consifyT t
    go pref (End l) = NE.singleton (pref, End l)
    go pref (ConsT l a suff) = (pref, End l) `NE.cons` go (SnocT pref a l) suff

valT :: Trace d -> Maybe (StateX d, ValX d)
valT t = go t
  where
    go t@ConsT{} = go (snocifyT t)
    go (End _) = Nothing
    go (SnocT t a l) = case a of
      ValA v    -> Just (tgt t, v)
      App1A{}   -> Nothing
      App2A{}   -> Nothing
      BindA{}   -> Nothing
      LookupA{} -> Nothing
      UpdateA{} -> go t

val :: Trace d -> Maybe (ValX d)
val t = snd <$> valT t

type (:->) = Map
infixr :->

type Env = Map Name

tracesAt :: HasLabel (StateX d) => Label -> Trace d -> [Trace d]
tracesAt l t = case t of
  End l' -> [t | l == labelOf l']
  ConsT l' a t' -> [End l' | l == labelOf l'] ++ map (ConsT l' a) (tracesAt l t')
  SnocT t' a l' -> tracesAt l t' ++ [SnocT t' a l' | l == labelOf l']

-- | Derive the pointwise prefix trace semantics from a maximal and inifinite
-- trace semantics (Section 6.12 of POAI).
pointwise :: HasLabel (StateX d) => (LExpr -> Trace d -> Trace d) -> LExpr -> Trace d -> Label -> [Trace d]
pointwise sem e p l = map (concatT p) $ tracesAt l $ sem e p

-- | Turns a maximal finite or infinite trace into the list of its prefix
-- traces. The list is finite iff the incoming trace is.
prefs :: Trace d -> NonEmpty (Trace d)
prefs = go
  where
    go t = case t of
      End l -> NE.singleton t
      ConsT l a t' -> End l `NE.cons` fmap (ConsT l a) (go t')
      SnocT{} -> go (consifyT t)

traceLabels :: HasLabel (StateX d) => Trace d -> NonEmpty Label
traceLabels = go
  where
    go (End l) = pure (labelOf l)
    go (ConsT l _ t) = labelOf l `NE.cons` go t
    go t@SnocT{} = go (consifyT t)

traceStates :: Trace d -> NonEmpty (StateX d)
traceStates = go
  where
    go (End s) = pure s
    go (ConsT s _ t) = s `NE.cons` go t
    go t@SnocT{} = go (consifyT t)

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


-- REMINDER: This definition becomes insufficient as soon as we introduce black-holing.
-- Then we'd also need to consider variables bound in Update frames on the stack.
freshName :: Name -> Name :-> a -> Name
freshName n h = go n
  where
    go n
      | n `Map.member` h = go (n ++ "'")
      | otherwise = n

freshAddr :: Addr :-> a -> Addr
freshAddr h = Map.size h

splitBalancedPrefix :: HasLabel (StateX d) => Show d => Trace d -> (Trace d, Maybe (Trace d))
splitBalancedPrefix p = -- traceIt (\(r,_)->"split" ++ "\n"  ++ show (takeT 3 p) ++ "\n" ++ show (takeT 3 r)) $
  work (consifyT p)
  where
    traceIt f res = trace (f res) res
    work p@(End _) = (p, Nothing) -- Not balanced
    work p'@(ConsT l a p) = case a of
      ValA _ -> (ConsT l a (End (src p)), Just p) -- balanced
      BindA{}   -> first (ConsT l a) (work p)
      App1A{} ->
        -- we have to be extremely careful not to force mp2 too early
        let (p1, mp2) = work p
            pref = ConsT l a p1
            (suff, mp') = case mp2 of
              Just (ConsT l2 (App2A x) p2) ->
                let (p3, mp4) = work p2
                 in (ConsT l2 (App2A x) p3,mp4)
              _ -> (End (tgt p1), Nothing)
         in (pref `concatT` suff,mp')
      LookupA a ->
        let (p1, mp2) = work p
            pref = ConsT l (LookupA a) p1
            (suff, mp') = case mp2 of
              Just (ConsT l2 (UpdateA a) p2) ->
                -- NB: In contrast to App1A, we don't need to end with a
                --     balanced p2
                (ConsT l2 (UpdateA a) (End (src p2)), Just p2)
              _ -> (End (tgt p1), Nothing)
         in (pref `concatT` suff,mp')
      App2A _   -> (p',Nothing) -- Not balanced; one closing parens too many
      UpdateA{} -> (p',Nothing) -- Not balanced; one closing parens too many

-- | Loop indefinitely for infinite traces!
isBalanced :: HasLabel (StateX d) => (Eq (Trace d), Show d) => Trace d -> Bool
isBalanced p = case splitBalancedPrefix p of
  (p', Just (End l)) | labelOf l == labelOf (tgt p) -> p' == p
  _                                                 -> False

data Lifted a = Lifted !a
              | Bottom
              deriving (Eq, Ord, Show)

varOccs :: Expr -> Set Name
varOccs e = go Set.empty e
  where
    go vs (FVar x) = Set.insert x vs
    go vs (FApp e x) = go (Set.insert x vs) e
    go vs (FLam x e) = go (Set.insert x vs) e
    go vs (FLet x e1 e2) = go (go (Set.insert x vs) e1) e2

letBoundVars :: Expr -> Set Name
letBoundVars e = go Set.empty e
  where
    go vs (FVar x) = vs
    go vs (FApp e x) = go vs e
    go vs (FLam x e) = go vs e
    go vs (FLet x e1 e2) = go (go (Set.insert x vs) e1) e2

uniqify :: Expr -> Expr
uniqify e = evalState (go Map.empty e) Set.empty
  where
    taken = varOccs e
    go benv (FLet n e1 e2) = do
      n' <- freshen n
      let benv' = Map.insert n n' benv
      FLet n' <$> go benv' e1 <*> go benv' e2
    go benv (FLam n e) = do
      n' <- freshen n
      let benv' = Map.insert n n' benv
      FLam n' <$> go benv' e
    go benv (FVar n) =
      pure (FVar (Map.findWithDefault n n benv))
    go benv (FApp e n) =
      FApp <$> go benv e <*> pure (Map.findWithDefault n n benv)
    freshen n = do
      s <- get
      let try n | Set.member n s = try (n ++ "'")
                | otherwise      = n
      let n' = try n
      put (Set.insert n' s)
      pure n'

-- | A wrapper indicating that this thing does not influence the semantics in
-- any way and is just there to carry constructive proof for use in the Galois
-- Abstraction
newtype SemanticallyIrrelevant a = SI { useSemanticallyIrrelevant :: a } deriving (Eq, Show)

-- | An address we promise to *never* look at in `run`.
-- It is only there so that we can write the bijection to Stateful semantics.
type SIAddr = SemanticallyIrrelevant Addr

-- | Wraps a function `f` such that it returns the dependent sum `∃a.f a`,
-- allowing us to extract both the `b = f a` and the `a` from whence it came
-- via `tgtInv`
mkInvertible :: (a -> b) -> (a -> (SemanticallyIrrelevant a, b))
mkInvertible f a = (SI a, f a)

-- | Corresponds to the dependent sum (∃p.tgt p),
-- allowing us to extract both the s = tgt p and the p from whence it came
-- via `tgtInv`
tgt' :: Trace d -> (SemanticallyIrrelevant (Trace d), StateX d)
tgt' = mkInvertible tgt

tgtInv :: Show (StateX d) => HasCallStack => HasLabel (StateX d) => (SemanticallyIrrelevant (Trace d), StateX d) -> Trace d
tgtInv (SI p, s) = p

orElse = flip fromMaybe
infixl 1 `orElse`

mapTraceWithPrefixes
  :: HasLabel (StateX d1)
  => (Trace d1 -> StateX d2) -- ^ Map an old prefix to a new state
  -> (StateX d1 -> Action d1 -> StateX d1 -> Action d2) -- ^ Map an action and its before/after state to a new action
  -> Trace d1 -- ^ old trace
  -> Trace d2 -- ^ new state
mapTraceWithPrefixes st act p = go End p
  where
    go mk_pref p = case p of
      ConsT s a p' ->
        let pref = mk_pref s
        in sum (traceLabels pref) `seq` ConsT (st pref) (act s a (src p')) (go (SnocT pref a) p')
      End s -> End (st (mk_pref s))
      SnocT p' a s -> SnocT (go mk_pref p') (act (tgt p') a s) (st (mk_pref (src p') `concatT` p))

---- | Potential liveness abstraction
--absL :: Set Name -> Trace d -> Set Name
--absL liveAtEnd p = go Map.empty (consifyT p)
--  where
--    go env (End l) = liveAtEnd
--    go env (ConsT l a p) = case a of
--      BindA n addr _ -> go (Map.insert addr n env) p
--      LookupA addr   -> Set.insert (env Map.! addr) (go env p)
--      _              -> go env p

traceWith f a = trace (f a) a
