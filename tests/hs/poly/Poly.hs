module Poly where

-- Safe subtraction in a package (spec): a polymorphic def's copies at Int
-- (HsInt, exact below zero) and at Natural (an error below zero) keep their
-- own subtraction; a def at Int, HsInt, its own.

import Numeric.Natural (Natural)

distP :: (Ord a, Num a) => a -> a -> a
distP a b = if a < b then b - a else a - b

gapP :: Num a => a -> a -> a
gapP a b = abs (a - b)

maxP :: (Ord a, Num a) => a -> a -> a
maxP a b = max 0 (a - b)

facP :: (Eq a, Num a) => a -> a
facP 0 = 1
facP n = n * facP (n - 1)

useD :: Int -> Int -> Int
useD a b = distP a b

useG :: Int -> Int -> Int
useG a b = gapP a b

useM :: Int -> Int -> Int
useM a b = maxP a b

useN :: Natural -> Natural -> Natural
useN a b = distP a b

useNM :: Natural -> Natural -> Natural
useNM a b = maxP a b

useF :: Natural -> Natural
useF n = facP n

gapI :: Int -> Int -> Int
gapI a b = abs (a - b)

monI :: Int -> Int -> Int
monI a b = max 0 (a - b)

down :: Int -> [Int]
down n | n <= 0 = []
       | otherwise = n : down (n - 1)

neg :: Int -> Int -> Int
neg a b = if a < b then a - b else b - a
