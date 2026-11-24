module IntNeg where

-- The ways an Int can go below 0 from non-negative inputs.  F takes an
-- Int to Bend's Nat only where none is used (Survey.bend's int-sub: the
-- hypothesis adj/PROPOSED.bend's agree proves enough for G -| F at Int),
-- so each def here is signed (HsInt) or out, and none answers otherwise
-- than GHC through G(F(h)).

import Data.Bits (complement)

decr :: Int -> Int
decr x = x - 1

minus1 :: Int -> Int
minus1 x = subtract 1 x

neg :: Int -> Int
neg x = negate x

before :: Int -> Int
before x = pred x

lit :: Int -> Int
lit x = x + (-3)

flipped :: Int -> Int
flipped x = complement x

parsed :: String -> Int
parsed s = read s

-- through another def that subtracts
viaDecr :: Int -> Int
viaDecr x = decr x * 2

-- through Integer
viaInteger :: Int -> Int
viaInteger x = fromInteger (toInteger x - 5)

-- an enumeration downward
countdown :: Int -> [Int]
countdown n = [n, n - 1 .. 0]

-- what agrees: no subtraction
double :: Int -> Int
double x = x * 2 + 1

halfOf :: Int -> Int
halfOf x = x `div` 2

-- Int's wrap-around: outside the model (its Int is Integer's)
big :: Int -> Int
big x = x * 4611686018427387904
