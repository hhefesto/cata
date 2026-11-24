module HofSec where

-- list functions at a section or a partial application over run-time locals:
-- `takeWhile (/= d) xs`, `map (scale k) xs`, `foldr (step k) z xs`, the same
-- recursion as at a lambda (Spec's sp.hf), and Map's adjust and insertWith,
-- which run their function at most once, at a closure

import Data.Map (Map)
import qualified Data.Map as Map

splitOn :: Char -> String -> [String]
splitOn d xs = go xs
  where
    go [] = []
    go ys =
      let w = takeWhile (/= d) ys
          r = dropWhile (/= d) ys
       in w : (case r of { [] -> []; _ : t -> go t })

scale :: Int -> Int -> Int
scale k x = k * x + 1

scales :: Int -> [Int] -> [Int]
scales k xs = map (scale k) xs

above :: Int -> [Int] -> [Int]
above k xs = filter (> k) xs

anyIs :: Int -> [Int] -> Bool
anyIs k xs = any (== k) xs

step :: Int -> Int -> Int -> Int
step k x acc = k * acc + x

horner :: Int -> [Int] -> Int
horner k xs = foldr (step k) 0 xs

addAll :: Int -> [Int] -> [Int]
addAll k xs = zipWith (step k) xs (map (+ k) xs)

bump :: Int -> String -> Map String Int -> Map String Int
bump k s m = Map.adjust (\v -> v * v + k) s m

count :: Int -> String -> Map String Int -> Map String Int
count k s m = Map.insertWith (\new old -> old + new * k) s k m

counts :: Int -> [String] -> [(String, Int)]
counts k ss = Map.toList (bump k "b" (foldr (count k) Map.empty ss))

longer :: Int -> [String] -> [String]
longer n = filter ((> n) . length)

-- a local function that uses a value only the run has, by name
render :: Int -> [(String, Int)] -> [String]
render gutter rows = map line rows
  where
    width = foldr (max . length . fst) 0 rows + gutter
    pad s = s ++ replicate (max 0 (width * 1) `seqNat` length s) ' '
    line (n, k) = pad n ++ show k

seqNat :: Int -> Int -> Int
seqNat w l = if l < w then subNat w l else 0

subNat :: Int -> Int -> Int
subNat w l = case l of
  0 -> w
  _ -> length (drop l (replicate w ()))

keep :: Int -> [Int] -> [Int]
keep k xs = filter ok xs
  where ok x = x > k || x == 0

-- a list function without its list, and uncurry at a closure
comp :: Int -> ([Int], Int) -> [Int]
comp k = map (scale k) . fst

comps :: Int -> [([Int], Int)] -> [[Int]]
comps k ps = map (filter (> k) . fst) ps

dists :: Int -> (Int, Int) -> Int
dists k p = uncurry (step k) p
