-- | Rational (Data.Ratio's Ratio Integer) as HsPrelude's HsRational: the
-- arithmetic, comparisons, numerator and denominator, %, gcd and lcm, show
-- (telomare's EAL solves its box constraints by a simplex over Rational).
module Rat where

import Data.Ratio (denominator, numerator, (%))

-- the row's coefficients scaled to integers by their denominators' lcm
-- (EAL's scaleRow)
scaleRow :: [(Int, Rational)] -> [(Int, Integer)]
scaleRow xs = [(v, numerator (x * fromInteger scale)) | (v, x) <- xs]
  where
    scale = foldr (lcm . denominator . snd) 1 xs

-- a pivot step: r - (r's coefficient / p's) p
eliminate :: Rational -> [Rational] -> [Rational] -> [Rational]
eliminate k p r = zipWith (\a b -> b - k * a) p r

ratio :: Integer -> Integer -> Rational
ratio a b = a % b

half :: Rational -> Rational
half x = x / 2

avg :: Rational -> Rational -> Rational
avg a b = (a + b) / 2

clampPos :: Rational -> Rational
clampPos x = if x < 0 then negate x else x

best :: [Rational] -> Rational
best = foldr max 0

showR :: Rational -> String
showR = show

fromInt :: Int -> Rational
fromInt n = fromIntegral n

ex1 :: [(Int, Integer)]
ex1 = scaleRow [(1, 1 % 2), (2, 2 % 3), (3, (-5) % 6)]

ex2 :: [Rational]
ex2 = eliminate (3 % 4) [1, 2 % 3] [5 % 2, 7]

ex3 :: String
ex3 = showR (ratio 6 (-4))

ex4 :: Rational
ex4 = avg (1 % 3) (1 % 6)

ex5 :: Bool
ex5 = best [1 % 2, 2 % 3, (-1) % 1] == 2 % 3
