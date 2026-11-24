module HofCopy where

import Data.List (find, sortBy)
import Data.Maybe (mapMaybe)

-- A list function's lambda that uses its element, or its accumulator, more
-- than once (Bend's + on the binder).

m1 :: [Int] -> [Int]
m1 xs = map (\x -> x * x + x) xs

f1 :: [Int] -> [Int]
f1 xs = filter (\x -> x > 1 && x < 3) xs

a1 :: [Int] -> Bool
a1 xs = any (\x -> x > 1 && x < 3) xs

a2 :: [Int] -> Bool
a2 xs = all (\x -> x < 1 || x > 2) xs

r1 :: [Int] -> Int
r1 xs = foldr (\x acc -> x * x + acc * acc) 1 xs

r2 :: [Int] -> Int
r2 xs = foldr (\x acc -> if x > acc then x else acc) 0 xs

l1 :: [Int] -> Int
l1 xs = foldl (\acc x -> if x > acc then x else acc) 0 xs

l2 :: [Int] -> Int
l2 xs = foldl (\acc x -> acc * acc + x * x) 1 xs

l3 :: [Char] -> Int
l3 = foldl (\acc d -> acc * 2 + if d == '1' then 1 else 0) 0

z1 :: [Int] -> [Int] -> [Int]
z1 xs ys = zipWith (\x y -> x * x + y * y) xs ys

c1 :: [Int] -> [Int]
c1 xs = concatMap (\x -> [x, x + 1]) xs

t1 :: [Int] -> [Int]
t1 xs = takeWhile (\x -> x > 0 && x < 3) xs

d1 :: [Int] -> [Int]
d1 xs = dropWhile (\x -> x > 0 && x < 3) xs

n1 :: [Int] -> Maybe Int
n1 xs = find (\x -> x > 1 && x < 3) xs

p1 :: [Int] -> [Int]
p1 xs = mapMaybe (\x -> if x > 1 then Just (x * x) else Nothing) xs

-- partial ones
q1 :: [Int] -> [Int]
q1 xs = map (\x -> (6 `div` x) + x) xs

q2 :: [Int] -> [Int]
q2 xs = filter (\x -> x > 4 `div` x) xs

q3 :: [Int] -> Bool
q3 xs = any (\x -> x > 4 `div` x) xs

q4 :: [Int] -> Bool
q4 xs = all (\x -> x > 4 `div` x) xs

q5 :: [Int] -> Int
q5 xs = foldr (\x acc -> (acc * acc + x) `div` x) 1 xs

q6 :: [Int] -> Int
q6 xs = foldl (\acc x -> (acc * acc + x) `div` x) 1 xs

q7 :: [Int] -> [Int] -> [Int]
q7 xs ys = zipWith (\x y -> (x * x + y) `div` y) xs ys

q8 :: [Int] -> [Int]
q8 xs = mapMaybe (\x -> if x > 3 `div` x then Just (x * x) else Nothing) xs
