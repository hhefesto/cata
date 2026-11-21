module Maps where

-- cata's Data.Map and Data.Set functions after the first ones
-- (prelude/HsMapMore.bend): telomare's uses (EAL's split, withoutKeys,
-- intersectionWith, fromSet, IntMap's unionsWith; Resolve's restrictKeys,
-- Set's intersection, unionWithKey)

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set

pairs :: String -> [(String, Int)]
pairs s = zip (map (: []) s) [1 ..]

m1 :: String -> Map.Map String Int
m1 s = Map.fromList (pairs s)

ex1 :: String -> String -> [(String, (Int, Int))]
ex1 a b = Map.toList (Map.intersectionWith (,) (m1 a) (m1 b))

ex2 :: String -> String -> [(String, Int)]
ex2 a b = Map.toList (Map.restrictKeys (m1 a) (Set.fromList (map (: []) b)))

ex3 :: String -> String -> [(String, Int)]
ex3 a b = Map.toList (Map.withoutKeys (m1 a) (Set.fromList (map (: []) b)))

ex4 :: String -> [(String, Int)]
ex4 a = Map.toList (Map.fromSet length (Set.fromList (words a)))

ex5 :: String -> String -> [(String, Int)]
ex5 a b = Map.toList (Map.unionWithKey (\k x y -> length k + x * 10 + y) (m1 a) (m1 b))

ex6 :: [Int] -> [Int] -> [(Int, Int)]
ex6 xs ys = IntMap.toList (IntMap.unionsWith (-) [IntMap.fromList (zip xs ys), IntMap.fromList (zip ys xs), IntMap.singleton 0 7])

ex7 :: String -> String -> ([(String, Int)], [(String, Int)])
ex7 k a = case Map.split k (m1 a) of
  (lo, hi) -> (Map.toList lo, Map.toList hi)

ex8 :: Int -> [Int] -> [Int]
ex8 v xs = IntMap.elems (snd (IntMap.split (v - 1) (IntMap.fromList (zip xs xs))))

ex9 :: String -> String -> [String]
ex9 a b = Set.toList (Set.fromList (words a) `Set.intersection` Set.fromList (words b))

ex10 :: String -> String -> Bool
ex10 a b = not (Set.null (Set.fromList (words a) `Set.intersection` Set.fromList (words b)))
