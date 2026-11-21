module Partial where

-- Partial functions as telomare writes them: error at a case's or a
-- guard's answer (Size's term3ToUnsizedExpr, Indent's indentTail),
-- Data.Map's ! inside an expression (EAL's simplex), !! at an if's
-- branch (Levels' offAt), head and fromJust, and calls of partial defs
-- from other defs, in a let and in an argument.

import qualified Data.Map as Map
import Data.Maybe (fromJust)

data Shape = Dot | Line Int | Box Int Int

width :: Shape -> Int
width s = case s of
  Line n -> n
  Box w _ -> w
  _ -> error "width: a dot has none"

-- a guard's answer
half :: Int -> Int
half n
  | n `mod` 2 == 0 = n `div` 2
  | otherwise = error ("half: odd " ++ show n)

-- callers: in an argument, in a let, twice
ex1 :: Shape -> Int
ex1 s = width s + 1

ex2 :: Int -> Int
ex2 n = let h = half n in h * h

ex3 :: Int -> Int -> Int
ex3 a b = half a + half b

-- Map's ! inside an expression
look :: Map.Map Int Int -> Int -> Int
look m k = m Map.! k + 1

ex4 :: Int -> Int
ex4 k = look (Map.fromList [(1, 10), (2, 20)]) k

-- !! at an if's branch
offAt :: [Int] -> Int -> Int
offAt offs j = if j < length offs then offs !! j else 0

ex5 :: Int -> Int
ex5 j = offAt [5, 6, 7] j

-- head and fromJust
firstOr :: [Int] -> Int
firstOr xs = head xs * 2

ex6 :: Int -> Int
ex6 n = firstOr (replicate n 3)

ex7 :: Maybe Int -> Int
ex7 m = fromJust m + 1

-- a total caller of a total def stays total
ex8 :: Int -> Int
ex8 n = n + 1

-- a comprehension (the specialiser's concatMap copy, its element a lambda
-- applied at once)
ex9 :: [Int] -> [Int]
ex9 xs = [half x + 1 | x <- xs]

-- a partial function as a function argument: out for now
-- (fold:partial-in-lambda)
ex10 :: [Int] -> [Int]
ex10 xs = map half xs
