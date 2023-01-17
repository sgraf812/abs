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

import Expr
import ByName
import qualified Direct
import qualified Cont

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

estuck :: LExpr
estuck = label x

ew :: LExpr
ew = label $ let_ "y" (lam "x" (app x "x")) (app y "y")

ew2 :: LExpr
ew2 = label $ let_ "x" (app x "x") x

-- |
-- >>> e2
-- 1(let x = 6(λy. 7(y)8)9 in 2(3(4(x)5@x)@x))5
--
-- >>> takeT 20 $ Direct.maxinf e2 Map.empty (End (at e2))
-- [1]-BindA "x" 6 D->[2]-AppA "x"->[3]-AppA "x"->[4]-EnterA->[6]-ValA Fun->[9]-BetaA "y"->[7]-EnterA->[6]-ValA Fun->[9]-BetaA "y"->[7]-EnterA->[6]-ValA Fun->[9]
main :: IO ()
-- main = forM_ [e1, e2, estuck, ew, ew2] $ \e -> do
main = forM_ [e1, e2] $ \e -> do
  putStrLn "----------------"
  print e
  putStrLn "maximal and infinite trace"
  print $ takeT 15 $ Direct.maxinf e Map.empty (End (at e))
  putStrLn "smallStep"
  mapM_ print $ take 10 $ smallStep (unlabel e)
  putStrLn "tracesAt 2"
  mapM_ print $ tracesAt 2 $ takeT 10 $ Direct.maxinf e Map.empty (End (at e))
  putStrLn "defnSmallStep"
  mapM_ print $ take 10 $ defnSmallStep (unlabel e) (Direct.maxinf e Map.empty)
  putStrLn "splitBalancedExecution"
  --forM_ [1..20] $ \n -> print $ splitBalancedExecution (atToAfter e) $ takeT n $ Direct.maxinf e Map.empty (End (at e))
