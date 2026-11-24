-- a local function that takes a function, used at functions over run-time
-- locals and at two types (EAL's instantiateTemplate: shKV)
module LocHof where

import qualified Data.Map as Map

data T = V Int | P T T | D
  deriving (Eq, Show)

inst :: Int -> Map.Map Int T -> [(Int, Int)] -> (Map.Map Int T, [(Int, Int)])
inst base ts es = (Map.union (Map.fromAscList (fmap (shKV shT) (Map.toList ts))) ts, fmap (shKV sh) es)
  where
    sh i = if i >= 3 then i + base else i
    shT t = case t of
      V i -> V (sh i)
      P a b -> P (shT a) (shT b)
      D -> D
    shKV f (k, v) = (sh k, f v)

rounds :: Int -> [Int] -> Map.Map Int T -> Int
rounds _ [] m = Map.size m
rounds n (y : ys) m = case inst y m [(n, y)] of
  (m', es) -> sum (map snd es) + rounds (n + 1) ys m'

exRounds :: Int -> [Int] -> Int
exRounds n ys = rounds n ys (Map.fromList [(3, P (V 3) (V 1)), (n, D)])

exInst :: Int -> Int -> ([(Int, T)], [(Int, Int)])
exInst b n = case inst b (Map.fromList [(3, P (V 3) (V n)), (n, V n)]) [(n, 4), (5, n)] of (m, es) -> (Map.toList m, es)
