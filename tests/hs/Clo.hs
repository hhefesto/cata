-- | Closures handed to base's list functions: a lambda over a pattern's
-- variable, or over a parameter, as foldl's, foldr's and foldl''s
-- function (telomare's parseApplied: foldl (\a b -> x :< AppF a b) f
-- args). Each call is a copy of the model's def (prelude/Cata/Base.hs)
-- at the lambda, the variable its first parameter.
module Clo where

import Data.List (foldl')

data T = Leaf Int | App Int T T
  deriving (Eq, Show)

-- foldl at a lambda over a pattern's variable
apps :: (Int, [T]) -> T
apps (x, fargs) = case fargs of
  f : args -> foldl (\a b -> App x a b) f args
  [] -> Leaf x

-- foldr at a lambda over a parameter
scale :: Int -> [Int] -> [Int]
scale k = foldr (\a r -> k * a : r) []

-- foldl' at a lambda over two parameters
dot :: Int -> Int -> [Int] -> Int
dot k c xs = foldl' (\acc a -> acc + k * a + c) 0 xs

-- a closure inside a closure's body: foldr's lambda calls foldl at one
nest :: Int -> [[Int]] -> [Int]
nest k = foldr (\xs r -> foldl (\acc a -> acc + a * k) 0 xs : r) []

-- foldl at a known def, no free locals
total :: [Int] -> Int
total = foldl (+) 0

ex1 :: T
ex1 = apps (7, [Leaf 1, Leaf 2, Leaf 3])

ex2 :: [Int]
ex2 = scale 3 [1, 2, 3]

ex3 :: Int
ex3 = dot 2 1 [1, 2, 3]

ex4 :: [Int]
ex4 = nest 2 [[1, 2], [], [3]]

ex5 :: Int
ex5 = total [4, 5, 6]
