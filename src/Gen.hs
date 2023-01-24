module Gen where

import           Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Char
import Text.Show

import Expr
import GHC.Stack

newtype Env = Env { nextFree :: Int }

instance Show Env where
  showsPrec _ = showListWith showString . boundVars

idx2Name :: Int -> Name
idx2Name n | n <= 26   = [chr (ord 'a' + n)]
           | otherwise = "t" ++ show n

boundVars :: Env -> [Name]
boundVars (Env n) = map idx2Name [0..n-1]

mkEnvWithNVars :: Int -> Env
mkEnvWithNVars = Env

emptyEnv :: Env
emptyEnv = mkEnvWithNVars 0

env :: Gen Env
env = Gen.sized $ \size -> Gen.element (map mkEnvWithNVars [0..max 0 (unSize size)])

closedExpr :: Gen Expr
closedExpr = openExpr emptyEnv

openExpr :: Env -> Gen Expr
openExpr env = Gen.sized $ \size ->
  Gen.frequency $ concat
    -- [ [ (1, freeName env)  ] -- let's not worry about "constants"
    [ [ ((unSize size `div` 8) + 2, boundName env) | not $ null $ boundVars env ]
    , [ ((unSize size `div` 4) + 1, let_ env) ]
    , [ ((unSize size `div` 4) + 1, lam env)      ]
    , [ ((unSize size `div` 4) + 1, app env)  | not $ null $ boundVars env ]
    ]

-- | This defn leads to good correlation between Gen size and expr sizes
letFactor :: Size -> Size
letFactor n = n*16 `div` 31

myElement :: HasCallStack => [a] -> Gen a
myElement = Gen.element

freeName, boundName, app, lam, let_ :: Env -> Gen Expr
freeName  env = Gen.element (map (Fix . Var . (:[])) ['A'..'Z']) -- upper case is never a bound var, but a constant
boundName env = Gen.element (map (Fix . Var) (boundVars env))
app       env = fmap Fix $
  App <$> Gen.scale (max 0 . subtract 1) (openExpr env)
      <*> Gen.element (boundVars env)
lam       env = fmap Fix $ withBoundName env $ \v env' ->
  Lam v <$> Gen.scale (max 0 . subtract 1) (openExpr env')
let_      env = fmap Fix $ withBoundName env $ \v env' ->
  Let v <$> Gen.small (openExpr env')
        <*> Gen.small (openExpr env')

withBoundName :: Env -> (Name -> Env -> Gen a) -> Gen a
withBoundName env f = Gen.choice $ fresh : [ shadowing | not $ null $ boundVars env ]
  where
    fresh = do
      let tv   = idx2Name (nextFree env)
          env' = env { nextFree = nextFree env + 1 }
      f tv env'
    shadowing = do
      tv <- Gen.element (boundVars env)
      f tv env

isqrt :: Int -> Int
isqrt = floor . sqrt . fromIntegral

exprDepth :: Expr -> Int
exprDepth (Fix (Var _)) = 0
exprDepth (Fix (App f a)) = 1 + exprDepth f
exprDepth (Fix (Lam _ e)) = 1 + exprDepth e
exprDepth (Fix (Let _ e1 e2)) = 1 + max (exprDepth e1) (exprDepth e2)

exprSize :: Expr -> Int
exprSize (Fix (Var _)) = 1
exprSize (Fix (App f a)) = 1 + exprSize f
exprSize (Fix (Lam _ e)) = 1 + exprSize e
exprSize (Fix (Let _ e1 e2)) = 1 + exprSize e1 + exprSize e2

