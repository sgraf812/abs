{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TestMain (main) where

import           Hedgehog hiding (label)
import           Hedgehog.Gen (sized)
import           Control.Monad
import qualified Gen
import           Control.Monad.IO.Class
import           Debug.Trace
import qualified Data.Map as Map

import           Expr
import           ByNeed
import           Direct
import Data.Maybe

main :: IO ()
main = void $
  checkParallel $$(discover)

sizeFactor :: Int
sizeFactor = 1

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
    let absSmallStep e = defnSmallStep e (maxinf (label e) Map.empty)
    take (sizeFactor*50) (smallStep e) === take (sizeFactor*50) (absSmallStep e)

prop_maxinf_maximal_trace_stuck_or_balanced =
  property $ do
    e <- forAll Gen.closedExpr
    let le = label e
    let p = maxinf le Map.empty (End le.at)
    let p' = takeT (sizeFactor*100) p
    let maximal = p' == takeT (sizeFactor*101) p
    when (not maximal) discard
    let value = val p'
    let stuck = isJust value
    let balanced = isBalanced p'
    assert (stuck || balanced)
