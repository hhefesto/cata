module Until where

-- cata's rule for base's until: Base's model's until, written with fuel.
-- ex1 is Resolve's pruneBindings' shape: the names reachable from a seed,
-- a Set grown until it stops changing.

import qualified Data.Foldable as F
import qualified Data.Map as Map
import qualified Data.Set as Set

reach :: [(String, [String])] -> [String] -> [String]
reach bs seed = Set.toList (until (\s -> expand s == s) expand (Set.fromList seed))
  where
    bmap = Map.fromList [(n, Set.fromList ds) | (n, ds) <- bs]
    expand r = r <> F.fold (Map.restrictKeys bmap r)

graph :: [(String, [String])]
graph = [("a", ["b"]), ("b", ["c", "a"]), ("c", []), ("d", ["a"]), ("e", ["f"]), ("f", ["e"])]

ex1 :: String -> [String]
ex1 s = reach graph (words s)

ex2 :: Int -> Int
ex2 n = until (> 100) (\x -> x * 2 + 1) (abs n)
