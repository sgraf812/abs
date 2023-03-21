{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module TestMain (main) where

import           Hedgehog hiding (label)
import           Hedgehog.Gen (sized, int)
import           Control.Monad
import qualified Gen
import           Control.Monad.IO.Class
import           Debug.Trace
import qualified Data.Map as Map
import           Data.Maybe
import           Data.String
import           Text.Printf
import           Control.Concurrent
import           Control.Concurrent.Async.Lifted (race)

import           Expr hiding (assert)
import           Stateless
import qualified Cont
import qualified Stateful
import qualified Data.List.NonEmpty as NE
import qualified TooEarlyStateless
import Hedgehog.Range (constant)
import qualified DynamicEnv


main :: IO ()
main = void $
  checkParallel $$(discover)

sizeFactor :: Int
sizeFactor = 2

withTimeLimit :: Int -> TestT IO a -> TestT IO a
withTimeLimit timeout v = do
  result <-
    race
      (liftIO $ threadDelay timeout)
      v
  case result of
    Left () -> fail "Timeout exceeded"
    Right x -> pure x

prop_Eq_Expr =
  property $ do
    --e <- forAll (sized (\s -> trace (show s) Gen.closedExpr))
    --liftIO $ print (Gen.exprSize e)
    --liftIO $ print (Gen.exprDepth e)
    --liftIO $ print e
    e <- forAll Gen.closedExpr
    e === e

prop_maxinf_maximal_trace_stuck_or_balanced =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p = run le Map.empty (End le.at)
    let p' = takeT (sizeFactor*100) p
    let maximal = p' == takeT (sizeFactor*101) p
    let value = val p'
    let stuck = isNothing value
    let balanced = isBalanced p'
    --test $ withTimeLimit 10000 $ do
    test $ do
      assert (not maximal || stuck || balanced)
      classify "stuck" stuck
      classify "balanced" balanced
      classify "potentially infinite" (not maximal)
    --forM_ [0..20] $ \n ->
    --  classify (fromString (printf "larger than %3d" (20*n))) (Gen.exprSize e > 20*n)
    --forM_ [0..20] $ \n ->
    --  classify (fromString (printf "longer than %3d" (20*n))) (lenT p' > 20*n)

prop_maxinf_stateless_is_cont =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p1 = run le Map.empty (End le.at)
    let p2 = Cont.run le Map.empty (End le.at)
    let p1' = takeT (sizeFactor*100) p1
    let p2' = takeT (sizeFactor*100) p2
    p1' === Cont.concTrace p2'

prop_direct_cont_abs =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p = Cont.run le Map.empty (End le.at)
    let p' = takeT (sizeFactor*100) p
    p' === Cont.absTrace (Cont.concTrace p')

prop_stateful_maxinf =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p1 = Stateful.run le
    let p2 = run le Map.empty (End le.at)
    let p1' = NE.take (sizeFactor*100+1) p1
    let p2' = takeT (sizeFactor*100) p2
    let ignoring_dagger (Ret _,_,_,_) _ = True
        ignoring_dagger (E e,_,_,_)   l = e.at == l
    diff p1' (\a b -> length a == length b && and (zipWith ignoring_dagger a b)) (NE.toList $ traceLabels p2')

prop_cacheful_maxinf =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p1 = DynamicEnv.run le
    let p2 = run le Map.empty (End le.at)
    let p1' = NE.take (sizeFactor*100+1) p1
    let p2' = takeT (sizeFactor*100) p2
    let ignoring_dagger (Ret _,_,_,_) _ = True
        ignoring_dagger (E e,_,_,_)   l = e.at == l
    diff p1' (\a b -> length a == length b && and (zipWith ignoring_dagger a b)) (NE.toList $ traceLabels p2')

prop_too_early_stateless_maxinf =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p1 = TooEarlyStateless.runInit le
    let p2 = run le Map.empty (End le.at)
    let p1' = takeT (sizeFactor*100) p1
    let p2' = takeT (sizeFactor*100) p2
    let same_labels a b = traceLabels a == traceLabels b
    diff p1' same_labels p2'

prop_too_eraly_stateless_split_prefix =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    n <- forAll (int (constant 1 (sizeFactor*20)))
    let le = label e
    let p = TooEarlyStateless.runInit le
    let pref = takeT n p
    when (dst pref == returnLabel) discard -- indexAtLE doesn't work for daggerLabel
    let suff1 = dropT n p
    let suff2 = TooEarlyStateless.unD (TooEarlyStateless.run (indexAtLE (dst pref) le)) pref
    let p1 = takeT (sizeFactor*40) suff1
    let p2 = takeT (sizeFactor*40) suff2
    let is_pref a b = NE.toList (traceLabels a) `NE.isPrefixOf` traceLabels b
    diff p2 is_pref p1

eqListBy :: (a -> b -> Bool) -> [a] -> [b] -> Bool
eqListBy f []     []     = True
eqListBy f (x:xs) (y:ys) = f x y && eqListBy f xs ys
eqListBy _ _      _      = False

dropStuffTooEarlyStateless :: (Name :-> Addr, Addr :-> (Name :-> Addr, a)) -> (Name :-> Addr, Addr :-> (Name :-> Addr))
dropStuffTooEarlyStateless (env, heap) = (env, Map.map (\(env,_d) -> env) heap)

dropStuffDynamicEnv :: (Name :-> Addr, Addr :-> (a, Name :-> Addr, b)) -> (Name :-> Addr, Addr :-> (Name :-> Addr))
dropStuffDynamicEnv (env, heap) = (env, Map.map (\(_e,env,_d) -> env) heap)

prop_Stateful_materialisable_from_stateless =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    n <- forAll (int (constant 1 (sizeFactor*40)))
    let le = label e
    let ful  = map dropStuffDynamicEnv $ NE.take n $ Stateful.traceMemory $ Stateful.run le
    let less = map dropStuffTooEarlyStateless $ NE.take n $ TooEarlyStateless.traceStates $ TooEarlyStateless.runInit le
    let eq_state (fullenv, fullheap) (lessenv, lessheap) =
          fullenv == lessenv &&
          Map.map (\(_e,env,_d) -> env) fullheap == Map.map (\(env,_d) -> env) lessheap
    ful === less

