module SafeSub where

-- A subtraction that what is around it makes safe (Spec's sp.ssb): Nat's, in
-- a module alone too. The last ones are not safe, and are out (int-sub).

import Data.Char (isAsciiUpper, isDigit, ord)
import Numeric.Natural (Natural)

fac :: Integer -> Integer
fac 0 = 1
fac n = n * fac (n - 1)

fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

count :: Int -> [Int]
count n
  | n <= 0 = []
  | otherwise = n : count (n - 1)

dist :: Int -> Int -> Int
dist a b = if a < b then b - a else a - b

gap :: Int -> Int -> Int
gap a b = abs (a - b)

monus :: Int -> Int -> Int
monus a b = max 0 (a - b)

floorTo :: Int -> Int -> Int
floorTo a b = max (a - b) 3

takeN :: Int -> [a] -> [a]
takeN n _ | n <= 0 = []
takeN _ [] = []
takeN n (x : xs) = x : takeN (n - 1) xs

between :: Int -> Int -> Int -> Int
between lo hi x
  | x < lo || x > hi = 0
  | otherwise = x - lo + (hi - x)

bothTests :: Int -> Int -> Int
bothTests a b = if a >= 2 && not (b == 0) then (a - 2) * (b - 1) else 7

viaCase :: Int -> Int
viaCase n = case n of
  0 -> 10
  1 -> 11
  _ -> n - 2

digit :: Char -> Int
digit c = if isDigit c then ord c - ord '0' else 0

letter :: Char -> Int
letter c
  | isAsciiUpper c = ord c - 65
  | 'a' <= c && c <= 'z' = ord c - ord 'a'
  | otherwise = 99

natGap :: Natural -> Natural -> Natural
natGap a b = if a < b then b - a else a - b

natDown :: Natural -> [Natural]
natDown 0 = [0]
natDown n = n : natDown (n - 1)

strict :: Int -> Int -> Int
strict a b = if a < b then b - 1 else a

plusMinus :: Int -> Int
plusMinus n = (n + 3) - 2

same :: Int -> Int
same n = n - n

multi :: Int -> Int -> Int
multi a b
  | a > b, b > 3 = a - b - 1 + (b - 3)
  | otherwise = 0

whereN :: Int -> Int
whereN 0 = 5
whereN n = go 2
  where
    go k = k + (n - 1)

-- at a type variable (Integer, by the default rule)
distP :: (Ord a, Num a) => a -> a -> a
distP a b = if a < b then b - a else a - b

gapP :: Num a => a -> a -> a
gapP a b = abs (a - b)

maxP :: (Ord a, Num a) => a -> a -> a
maxP a b = max 0 (a - b)

-- not safe: out
pred1 :: Int -> Int
pred1 n = n - 1

wrongWay :: Int -> Int -> Int
wrongWay a b = if a < b then a - b else 0

lateGuard :: Int -> Int -> Int
lateGuard n m
  | m > 5 = n - 1
  | n <= 0 = 0
  | otherwise = n

fallsThrough :: Int -> Int -> Int
fallsThrough 0 b | b > 3 = 1
fallsThrough n _ = n - 1

otherArg :: Int -> [Int] -> Int
otherArg 0 [] = 1
otherArg n _ = n - 1

natMax :: Natural -> Natural -> Natural
natMax a b = max 0 (a - b)
