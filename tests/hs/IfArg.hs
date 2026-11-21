module IfArg where

-- Ifs and lets that are an application's argument: Spec moves them out
-- over it (EAL's mergeClasses: pure $ if la >= lb then a else b; a copy
-- at a known argument whose lambda's body is an if, as traverse's at a
-- pair).

pick :: Int -> Int -> Maybe Int
pick a b = pure $ if a >= b then a else b

dist :: Int -> Int -> Int
dist a b = 1 + (if a > b then a - b else b - a)

grow :: Int -> Int
grow n = negate (let m = n * 2 in m + 1)

both :: Int -> Int -> (Int, Int)
both a b = (if a > b then a else b, b)

lazyAnd :: Bool -> Int -> Bool
lazyAnd p n = p && (if n > 0 then n `mod` 2 == 0 else n < -5)

nested :: Int -> Int -> Int
nested a b = max (if a > 0 then a else negate a) (if b > 0 then b else 0)

halves :: [Int] -> [Int]
halves [] = []
halves (x : xs) = (if x `mod` 2 == 0 then x `div` 2 else x) : halves xs

ex1 :: Int -> Maybe Int
ex1 n = pick n (n * 3 - 7)

ex2 :: Int -> Int
ex2 n = dist n 5 + grow n + nested n (n - 3)

ex3 :: Int -> (Int, Int)
ex3 n = both n (10 - n)

ex4 :: Int -> [Int]
ex4 n = halves [n, n + 1, n * 3]
