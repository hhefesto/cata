-- Data.Map's and IntMap's map, filter, mapWithKey, .. at a function over
-- locals (EAL's pivot, eliminate), and a local function written point-free
-- (PrettyPrint's ind, EAL's merge)
module MapClo where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map as Map
import Data.List (intercalate)

type Row = IntMap.IntMap Int

scale :: Int -> Row -> Row
scale a = IntMap.filter (/= 0) . IntMap.map (a *)

combine :: Int -> Row -> Row -> Row
combine a prow row = IntMap.filter (\v -> v /= a) (IntMap.unionWith (+) row (IntMap.map (\x -> negate (a * x)) prow))

exCombine :: Int -> Int -> [(Int, Int)]
exCombine a b = IntMap.toList (combine a (IntMap.fromList [(1, b), (2, 3), (5, a)]) (IntMap.fromList [(1, a), (3, b), (5, 1)]))

addKey :: Int -> Map.Map Int Int -> Map.Map Int Int
addKey n m = Map.mapWithKey (\k v -> k * n + v) (Map.filterWithKey (\k v -> k + v > n) m)

exAddKey :: Int -> Int -> [(Int, Int)]
exAddKey n a = Map.toList (addKey n (Map.fromList [(a, 1), (2, a), (3, 4)]))

sumFrom :: Int -> Map.Map Int Int -> Int
sumFrom n m = Map.foldr (\v r -> v * n + r) 0 m + Map.foldrWithKey (\k v r -> k - v * n - r) 1 (fmap (+ n) m)

exSumFrom :: Int -> Int -> Int
exSumFrom n a = sumFrom n (Map.fromList [(a, 1), (2, a), (7, 4)])

data Doc = Text String | Nest Doc Doc | Many [Doc]

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

render :: Int -> Doc -> String
render n d = go d where
  ind = indent n
  join = intercalate ","
  merge = Map.unionWith (+)
  go (Text s) = ind s
  go (Nest a b) = ind (go a) ++ ind (go b)
  go (Many ds) = join (map go ds) ++ show (Map.toList (merge (Map.singleton n 1) (Map.singleton 2 n)))

exRender :: Int -> String -> String
exRender n s = render n (Nest (Text s) (Many [Text "a", Nest (Text s) (Text "b")]))

-- at run-time values
exFold :: Int -> [Int] -> [(Int, Int)]
exFold n xs = IntMap.toList (go xs (IntMap.fromList [(1, n), (2, 3)])) where
  go [] m = m
  go (y : ys) m = go ys (combine y m (IntMap.map (\v -> v + y) m))

exKeys :: Int -> [Int] -> [(Int, Int)]
exKeys n xs = Map.toList (go xs (Map.fromList [(1, n), (2, 3)])) where
  go [] m = m
  go (y : ys) m = go ys (addKey (sumFrom y m) m)
