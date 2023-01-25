{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module TestMain (main) where

import           Hedgehog hiding (label)
import           Hedgehog.Gen (sized)
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

import           Expr
import           ByNeed
import           Direct


main :: IO ()
main = void $
  checkParallel $$(discover)

sizeFactor :: Int
sizeFactor = 1

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

prop_abs_smallstep_is_smallstep =
  property $ do
    e <- forAll Gen.closedExpr
    let defn e = defnSmallStep e (maxinf (label e) Map.empty)
    let abs e = absSmallStepEntry (label e)
    take (sizeFactor*50) (smallStep e) === take (sizeFactor*50) (defn e)
    take (sizeFactor*50) (smallStep e) === take (sizeFactor*50) (abs  e)

prop_maxinf_maximal_trace_stuck_or_balanced =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p = maxinf le Map.empty (End le.at)
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

prop_maxinf3_maximal_trace_stuck_or_balanced =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let le = label e
    let p = snd $ unD3 (maxinf3 le Map.empty) (End le.at)
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
