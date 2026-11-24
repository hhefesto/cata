module ListMore where

-- Data.List's splitAt, transpose, dropWhileEnd, uncons, scanl, elemIndex
-- (prelude/HsListMore.bend), divMod and quotRem (Spec's sp.divmod), the
-- arithmetic sequences (prelude/HsRange.bend), Data.Char's case maps
-- (prelude/HsChar.bend) and a local function at its one type (Spec's sp.lm)

import Data.Char (isSpace, toLower, toUpper)
import Data.List (dropWhileEnd, elemIndex, scanl, transpose, uncons)

chunks :: Int -> [a] -> [[a]]
chunks n xs = go (length xs) xs
  where
    go 0 _ = []
    go k ys = case splitAt n ys of
      ([], _) -> []
      (a, b) -> a : go (if k < n then 0 else length b) b

columns :: [[Int]] -> [[Int]]
columns = transpose

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

firstOf :: [Int] -> Maybe (Int, [Int])
firstOf = uncons

runs :: Int -> [Int] -> [Int]
runs z xs = scanl (+) z xs

place :: Char -> String -> Maybe Int
place c s = elemIndex c s

digits :: Int -> [Int]
digits n = case n `divMod` 10 of
  (0, r) -> [r]
  (q, r) -> digits q ++ [r]

parts :: Int -> Int -> (Int, Int)
parts a b = quotRem a b

halves :: Int -> (Int, Int)
halves n = let (q, r) = n `divMod` 2 in (q + r, q)

upto :: Int -> [Int]
upto n = [1 .. n]

between :: Int -> Int -> [Int]
between a b = [a .. b]

odds :: Int -> [Int]
odds n = [1, 3 .. n]

down :: Int -> [Int]
down n = [9, 7 .. n]

letters :: Char -> String
letters c = ['a' .. c]

table :: Int -> [(Int, Int)]
table n = [(a, b) | a <- [1 .. n], b <- [a .. n], even (a + b)]

shout :: String -> String
shout = map toUpper

lower :: String -> String
lower s = map toLower s ++ "\223\304\954"

lefts' :: [Either a b] -> [a]
lefts' = foldr onlyLeft []
  where
    onlyLeft (Left x) xs = x : xs
    onlyLeft _ xs = xs

biggest :: [Int] -> Int
biggest xs = go 0 xs
  where
    go m [] = m
    go m (y : ys) = go (if y > m then y else m) ys
