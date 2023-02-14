{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main (main) where

import ByNeed
import qualified Cont
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import qualified Direct
import qualified Stateful
import Expr
import Text.Show (showListWith)
import qualified Data.List.NonEmpty as NE

x, y, z, a, b, c, d, e, f, i, t :: Expr
x : y : z : a : b : c : d : e : f : i : t : _ = map (Fix . Var . (: [])) "xyzabcdefit"

app :: Expr -> Name -> Expr
app e n = Fix (App e n)

lam :: Name -> Expr -> Expr
lam n e = Fix (Lam n e)

let_ :: Name -> Expr -> Expr -> Expr
let_ n e1 e2 = Fix (Let n e1 e2)

e_1 :: LExpr
e_1 = label $ lam "y" y

e_2 :: LExpr
e_2 = label $ let_ "x" (lam "y" y) (app (app x "x") "x")

e_bool :: LExpr
e_bool = label $ let_ "t" (lam "a" (lam "b" a)) $
                 let_ "f" (lam "c" (lam "d" d)) $
                 app (app (app t "f") "t") "t"

e_fresh :: LExpr
e_fresh = label $ let_ "x" (lam "a" (let_ "y" a y)) $
                  let_ "z" (lam "c" c) $
                  let_ "d" (app x "x") $
                  let_ "e" (app x "z") $
                  app (app d "e") "d"

e_abs :: LExpr
e_abs = label $ read "let id = λx.x in let const = λy.λz.y in const const id"

e_stuck :: LExpr
e_stuck = label x

e_w :: LExpr
e_w = label $ let_ "x" x x

e_w2 :: LExpr
e_w2 = label $ let_ "x" (app x "x") x

e_W :: LExpr
e_W = label $ let_ "y" (lam "x" (app x "x")) (app y "y")

-- |
-- >>> e_2
-- 1(let x = 2(λy. 3(y))4 in 5(6(7(x) x) x))
--
-- >>> takeT 10 $ Direct.maxinf e_2 Map.empty (End (at e_2))
-- [1]-bind->[5]-app1->[6]-app1->[7]-look([1]_0)->[2]-val(fun)->[4]-app2->[3]-look([1]_0)->[2]-val(fun)->[4]-app2->[3]-look([1]_0)->[2]
main :: IO ()
main = forM_ [(10,e_1), (10,e_2), (10,e_stuck), (10,e_w), (10,e_w2), (10,e_W), (10,e_bool), (50,e_fresh), (50,e_abs)] $ \(n,e) -> do
-- main = forM_ [e_1, e2, e_stuck] $ \e -> do
  putStrLn "============================="
  putStrLn ""
  print e
  putStrLn ""
--  putStrLn "denotational semantics"
--  print $ ByName.denot (unlabel e) Map.empty
  putStrLn "-----------------------------"
  putStrLn "maximal and infinite trace (scary maximal trace semantics)"
  print $ takeT n $ Direct.maxinf e Map.empty (End (at e))
  putStrLn "-----------------------------"
  putStrLn "maximal and infinite trace continuation semantics"
  print $ takeT n $ Cont.unC (Cont.absD (Direct.maxinfD e Map.empty)) id (End (at e))
  putStrLn "-----------------------------"
  putStrLn "smallStep (transition system)"
  let ss1 = take n $ smallStep (unlabel e)
  mapM_ print ss1
  putStrLn "-----------------------------"
  putStrLn "stateful trace semantics"
  mapM_ print $ take n $ NE.toList $ Stateful.stateful e
  putStrLn "-----------------------------"
--  putStrLn "tracesAt 2"
--  mapM_ print $ tracesAt 2 $ takeT 10 $ Direct.maxinf e Map.empty (End (at e))
  putStrLn "defnSmallStep (derived from maximal trace)"
  let ss2 = take n $ defnSmallStep (unlabel e) (Direct.maxinf e Map.empty)
  mapM_ print ss2
  putStrLn "absSmallStep (derived from maximal trace semantics)"
  let ss2 = take n $ absSmallStepEntry e
  mapM_ print ss2
  putStrLn "-----------------------------"
  when (ss1 /= ss2) (error "NOT EQUAL")

--  putStrLn "splitBalancedPrefix"
--  forM_ [20,19..0] $ \m -> print $ fmap fst $ splitBalancedPrefix $ dropT m $ takeT n $ Direct.maxinf e Map.empty (End (at e))

  putStrLn "absS"
  mapM_ print $ Direct.absS $ takeT (n-1) $ Direct.maxinf e Map.empty (End (at e))

  putStr "dead: "
  print $ Set.difference (letBoundVars (unlabel e)) $ absL Set.empty $ takeT (n-1) $ Direct.maxinf e Map.empty (End (at e))
