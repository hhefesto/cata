module PartUnc where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map

data T = Leaf Int | Two T T | Hole
  deriving (Eq, Show)

type M = ExceptT String (State Int)

-- Hole is not covered
add :: Int -> T -> T -> M ()
add k (Leaf a) (Leaf b) = modify (+ (k + a + b))
add k (Two a b) (Two c d) = add k a c >> add k b d
add _ (Leaf _) (Two _ _) = throwError "mismatch"

addAll :: Int -> [(T, T)] -> M ()
addAll k ps = mapM_ (uncurry (add k)) ps

total :: [(T, T)] -> (Either String (), Int)
total ps = runState (runExceptT (addAll 1 ps)) 0

-- a Rational map with a partial division
scale :: Rational -> Map.Map Int Rational -> Map.Map Int Rational
scale p m = Map.map (/ p) m

-- forM over a Map's elements with a partial step, and a filter after
keepBig :: [T] -> [Int]
keepBig ts = map leafOf (filter (\t -> leafOf t > 2) ts)

leafOf :: T -> Int
leafOf (Leaf n) = n
leafOf (Two a _) = leafOf a

-- a fold whose step is partial
sumLeaves :: [T] -> Int
sumLeaves = foldl (\acc t -> acc + leafOf t) 0
