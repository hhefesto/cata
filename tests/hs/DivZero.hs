module DivZero where

-- div, mod, quot and rem by a divisor that may be 0: GHC throws
-- ArithException DivideByZero there, so F's Bend answers a failure value
-- (prelude/HsPartial.bend's HsNum, "divide by zero"); by a non-zero
-- literal they stay Base's total ones.  Rational's / at 0 throws
-- RatioZeroDenominator.  Before 11-23 F wrote Base's total Nat.div and
-- Nat.mod everywhere (x `div` 0 is 0, x `mod` 0 is x): more defined than
-- Haskell, and no left adjoint (adj/PROOF.bend, P.tot.not).

import Numeric.Natural (Natural)

-- by a literal: total
halve :: Int -> Int
halve n = n `div` 2

lastDigit :: Integer -> Integer
lastDigit n = n `mod` 10

-- by an argument: partial
ratio :: Int -> Int -> Int
ratio a b = a `div` b

remainder :: Int -> Int -> Int
remainder a b = a `mod` b

quotient :: Integer -> Integer -> Integer
quotient a b = a `quot` b

remq :: Integer -> Integer -> Integer
remq a b = a `rem` b

natDiv :: Natural -> Natural -> Natural
natDiv a b = a `div` b

isMultipleOf :: Int -> Int -> Bool
isMultipleOf d n = n `mod` d == 0

-- at Int with a subtraction (HsInt): flip div 2, the divisor known only
-- at flip (telomare's decendant), and by an argument
parent :: Int -> Int
parent x = flip div 2 (pred x)

signedDiv :: Int -> Int -> Int
signedDiv a b = (a - 3) `div` b

-- a caller of a partial one is partial
avg :: Int -> Int -> Int
avg total count = ratio total count + 1

frac :: Rational -> Rational -> Rational
frac a b = a / b
