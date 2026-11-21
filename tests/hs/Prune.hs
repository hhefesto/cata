module Prune where

-- Resolve's pruneBindings and freeVarsDeep, in their shapes: a local
-- function (expand) the arguments of until name, a lambda over a local
-- function (refs) foldMap takes, filter at a section over a local.

import Data.Bifunctor (second)
import qualified Data.Foldable as F
import qualified Data.Map as Map
import qualified Data.Set as Set

data T = V String | L String T | A T T | C T [(String, T)]

free :: T -> Set.Set String
free (V n) = Set.singleton n
free (L n b) = Set.delete n (free b)
free (A f x) = free f <> free x
free (C s alts) = free s <> foldMap (\(p, b) -> refs p <> free b) alts
  where
    refs p = Set.fromList [p, "and"]

prune :: T -> [(String, T)] -> [(String, T)]
prune root bs = filter ((`Set.member` reachable) . fst) bs
  where
    seed = free root
    bmap = Map.fromList $ fmap (second free) bs
    expand r = r <> F.fold (Map.restrictKeys bmap r)
    reachable = until (\s -> expand s == s) expand seed

env :: [(String, T)]
env =
  [ ("a", V "b"), ("b", A (V "c") (V "a")), ("c", L "x" (V "x"))
  , ("d", V "a"), ("e", C (V "f") [("g", V "e")]), ("f", V "e"), ("g", V "zz") ]

term :: String -> T
term s = foldr (\w t -> A (V w) t) (V "c") (words s)

ex1 :: String -> [String]
ex1 s = map fst (prune (term s) env)

ex2 :: String -> [String]
ex2 s = Set.toList (free (C (V s) [(s, L s (V "q")), ("r", term s)]))

ex3 :: String -> Int
ex3 s = length (prune (L "a" (term s)) env)

reach :: [(String, [String])] -> [String] -> [String]
reach bs seed = Set.toList (until (\s -> grow s == s) grow (Set.fromList seed))
  where
    m = Map.fromList [(n, Set.fromList ds) | (n, ds) <- bs]
    grow r = r <> F.fold (Map.restrictKeys m r)

ex4 :: String -> [String]
ex4 s = reach [("a", ["b"]), ("b", ["c", "a"]), ("d", ["a"])] (words s)
