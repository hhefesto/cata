module Stub where

-- Stubs at a function type, as hs1003's exercises leave them (00353's
-- fun1' = error "not implemented", 00166's matches = undefined): a def
-- with fewer parameters than arrows whose body is error's or undefined's
-- call alone.  The partial pass made its answer Either String (a -> b),
-- which Bend refuses (an Either holds Data, a function is Type); Fold's
-- fd.ee gives it a parameter for each arrow, and the error at the last
-- result, as GHC's answer is wherever the def is applied.  A caller given
-- every argument calls it once.

fun1' :: [Integer] -> Integer
fun1' = error "Week04.Soln#fun1' not implemented"

xor :: [Bool] -> Bool
xor = undefined

matches :: [Int] -> [Int] -> Int
matches = undefined

-- one parameter written, one arrow left
pad :: Int -> String -> String
pad n = error ("pad: " ++ show n)

-- a function argument (no input to list for it, so no law; it checks)
mapL :: (a -> b) -> [a] -> [b]
mapL f = undefined

-- callers, every argument given
useStub :: [Integer] -> Integer
useStub xs = fun1' xs + 1

both :: [Bool] -> [Bool] -> Bool
both a b = xor a && xor b

firstMatch :: [Int] -> Int
firstMatch xs = matches xs [1, 2, 3]
