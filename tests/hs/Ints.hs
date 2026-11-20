module Ints where

-- cata's signed Int (Spec writes Int and Integer as HsPrelude's HsInt):
-- negative literals and patterns, subtraction, Haskell's div/mod/quot/rem,
-- comparisons, show, IntMap and IntSet at it

import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet

leftGate :: Int
leftGate = -2

offset :: Int -> Int -> Int
offset a b = a - b * 3

sign :: Int -> Int
sign 0 = 0
sign (-1) = -10
sign n = signum n * abs n

divs :: Int -> Int -> (Int, Int, Int, Int)
divs a b = if b == 0 then (0, 0, 0, 0) else (a `div` b, a `mod` b, a `quot` b, a `rem` b)

cmpI :: Int -> Int -> (Bool, Ordering, Int)
cmpI a b = (a < b, compare a b, max a b - min a b)

showI :: Int -> String
showI n = show (negate n) ++ show (n - 5)

big :: Integer -> Integer -> Integer
big a b = a * b - (a + b) ^ (2 :: Int)

pick :: [(Int, Int)] -> Int -> Maybe Int
pick xs k = IntMap.lookup k (IntMap.fromList xs)

shifted :: [(Int, Int)] -> [(Int, Int)]
shifted xs = IntMap.toList (IntMap.map (subtract 1) (IntMap.insert (-1) 0 (IntMap.fromList xs)))

uniqI :: [Int] -> [Int]
uniqI xs = IntSet.toList (IntSet.insert (-3) (IntSet.fromList xs))

countDown :: Int -> [Int]
countDown n = if n <= 0 then [] else n : countDown (n - 1)
