{-# LANGUAGE GADTs #-}

module Main where

import Data.Set
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
label (Fix e) = evalState 1 (lab e)
  where
    next :: StateT Label Label
    next = state (\l -> (l,l+1))
    lab :: ExprF Expr -> State Label LExpr
    lab e = do
      at <- next
      return _

data Action
  = Blah

data Trace
  = End !Label
  | Transition !Label !Action Trace

type D = Trace -> Set Trace

data Value = Fun (D -> D)

main :: IO ()
main = putStrLn "Hello, Haskell!"
