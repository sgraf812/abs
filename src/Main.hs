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
import qualified Stateless
import qualified Stateful
import Expr
import Text.Show (showListWith)
import qualified Data.List.NonEmpty as NE
import qualified DynamicEnv
import qualified Envless
import qualified Stackless
import qualified LessToFull
import System.IO

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
e_2 = label $ let_ "x" (lam "y" y) (app x "x")

e_3 :: LExpr
e_3 = label $ let_ "x" (lam "y" y) (app (app x "x") "x")

e_bool :: LExpr
e_bool = label $ let_ "t" (lam "a" (lam "b" a)) $
                 let_ "f" (lam "c" (lam "d" d)) $
                 app (app (app t "f") "t") "t"

e_fresh :: LExpr
-- The point here is that each call to id allocates
-- and has to give fresh heap entries for y
e_fresh = label $ read " let id = (λa. let y = a in y) in \
                       \ let z = λc.c in \
                       \ let d = id id in \
                       \ let e = id z in \
                       \ d e d"

e_abs :: LExpr
e_abs = label $ read "let id = λx.x in let const = λy.λz.y in const const id"

e_stuck :: LExpr
e_stuck = label x

e_stuck_app :: LExpr
e_stuck_app = label (read "a a")

e_stuck_let :: LExpr
e_stuck_let = label (read "let a = b in a")

e_w :: LExpr
e_w = label $ let_ "x" x x

e_w2 :: LExpr
e_w2 = label $ let_ "x" (app x "x") x

e_W :: LExpr
e_W = label $ let_ "y" (lam "x" (app x "x")) (app y "y")

e_bug1 :: LExpr
e_bug1 = label $ uniqify $ read "let a = (λb.let c = a in (let d = λe.a b in let f = let g = a in a in λh.let i = a in d) a) a in (let j = a in a) a"

e_bug2 :: LExpr
e_bug2 = label $ read "let a = a in let b = let c = a in a in b"

-- |
-- >>> e_2
-- 1(let x = 2(λy. 3(y))4 in 5(6(7(x) x) x))
--
-- >>> takeT 10 $ Stateless.stateless e_2 Map.empty (End (at e_2))
-- [1]-bind->[5]-app1->[6]-app1->[7]-look([1]_0)->[2]-val(fun)->[4]-app2->[3]-look([1]_0)->[2]-val(fun)->[4]-app2->[3]-look([1]_0)->[2]
main :: IO ()
main = forM_ [(15,e_1), (15,e_2), (15,e_3), (10,e_stuck), (10,e_w), (10,e_w2), (10,e_W), (10,e_bool), (50,e_fresh), (50,e_abs), (4,e_stuck_app), (20,e_stuck_let), (30, e_bug1), (15,e_bug2)] $ \(n,e) -> do
  putStrLn "============================="
  putStrLn ""
  print e
  putStrLn ""
--  putStrLn "denotational semantics"
--  print $ ByName.denot (unlabel e) Map.empty
  putStrLn "-----------------------------"
  putStrLn "maximal and infinite trace (scary maximal trace semantics)"
  let stateless = takeT n $ Stateless.run e Map.empty (End (E e))
  print stateless
  putStrLn "-----------------------------"
  putStrLn "maximal and infinite trace continuation semantics"
  let cont = takeT n $ Cont.unC (Cont.absD (Stateless.runD e Map.empty)) id (End (E e))
  print cont
  putStrLn "-----------------------------"
  putStrLn "stateful trace semantics"
  let stateful = takeT n $ Stateful.run e
  mapM_ print (traceStates stateful)
  putStrLn "-----------------------------"
  putStrLn "DynamicEnv"
  let dynamic_env = takeT n $ DynamicEnv.run e
  print dynamic_env
  putStrLn "-----------------------------"
  putStrLn "Envless"
  let envless = takeT n $ Envless.run e
  print envless
  putStrLn "-----------------------------"
  putStrLn "Stackless"
  let stackless = takeT n $ Stackless.run e
  print stackless
  putStrLn "-----------------------------"
  putStrLn "Bijection, Stateless after roundtrip"
  let stateless_round = LessToFull.backward $ LessToFull.forward stateless
  print stateless_round
  putStrLn "-----------------------------"
  putStrLn "Bijection, Stateful after roundtrip"
  let stateful_round = LessToFull.forward $ LessToFull.backward stateful
  mapM_ print (traceStates stateful_round)
  putStrLn "-----------------------------"
  when (traceLabels stateless /= traceLabels stateful) (error "stateless /= stateful")
  when (traceLabels stateless /= traceLabels dynamic_env) (error "stateless /= dynamic_env")
  when (traceLabels stateless /= traceLabels envless) (error "stateless /= envless")
  when (traceLabels stateless /= traceLabels stackless) (error "stateless /= stackless")
  when (traceLabels stateless /= traceLabels cont) (error "stateless /= cont")
  when (stateless /= stateless_round) (error "stateless /= stateless_round")
  when (stateful /= stateful_round) (error "stateful /= stateful_round")
  putStr "Testing abstraction"
  hFlush stdout
  forM_ [0..n] $ \m -> do
    putStr "."
    hFlush stdout
    let p1  = takeT m $ Stateless.runInit e
    let sp1 = LessToFull.forward p1
    let sp2 = takeT m $ Stateful.run e
    when (not $ Stateful.bisimilarForNSteps 20 sp1 sp2) (error ("forward " ++ show m))
    let sp1  = takeT m $ Stateful.run e
    let p1 = LessToFull.backward sp1
    let p2 = takeT m $ Stateless.runInit e
    when (not $ Stateless.bisimilarForNSteps 20 p1 p2) (error ("backward " ++ show m))
  putStrLn ""

--  putStrLn "tracesAt 2"
--  mapM_ print $ tracesAt 2 $ takeT 10 $ Stateless.stateless e Map.empty (End (at e))

--  putStrLn "splitBalancedPrefix"
--  forM_ [20,19..0] $ \m -> print $ fmap fst $ splitBalancedPrefix $ dropT m $ takeT n $ Stateless.stateless e Map.empty (End (at e))

--  putStrLn "absS"
--  mapM_ print $ TooEarlyStateless.absS $ takeT (n-1) $ TooEarlyStateless.stateless e Map.empty (End (at e))

--  putStr "dead: "
--  print $ Set.difference (letBoundVars (unlabel e)) $ absL Set.empty $ takeT (n-1) $ Stateless.run e Map.empty (End (at e))
