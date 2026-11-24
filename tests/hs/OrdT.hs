module OrdT where

-- compare at the module's own types: a derived Ord instance is T.cmp
-- (Fold's fd.cmp.def: the constructors in their order, then the fields
-- left to right), for <, <=, >, >=, compare, max and min, and as a Map's
-- and a Set's key; at Either, Ordering, a Map and a Set the prelude's.

import qualified Data.Map as Map
import qualified Data.Set as Set

data Color = Red | Green | Blue
  deriving (Eq, Ord, Show)

data Shape = Dot | Line Int | Box Int Bool | Many [Int] (Maybe Color)
  deriving (Eq, Ord, Show)

data Tree = Tip | Bin Tree Int Tree
  deriving (Eq, Ord, Show)

data P a b = P a b | Q b
  deriving (Eq, Ord, Show)

newtype Age = Age Int
  deriving (Eq, Ord, Show)

order :: Color -> Color -> Ordering
order = compare

less :: Shape -> Shape -> Bool
less a b = a < b

atMost :: Shape -> Shape -> Bool
atMost a b = a <= b

bigger :: Color -> Color -> Color
bigger a b = max a b

smaller :: Shape -> Shape -> Shape
smaller a b = min a b

trees :: Tree -> Tree -> Ordering
trees a b = compare a b

pairs :: P Int Color -> P Int Color -> Ordering
pairs a b = compare a b

older :: Age -> Age -> Bool
older a b = a > b

maxPair :: (Int, Color) -> (Int, Color) -> (Int, Color)
maxPair a b = max a b

eithers :: Either Int Color -> Either Int Color -> Ordering
eithers a b = compare a b

orderings :: Ordering -> Ordering -> Ordering
orderings a b = compare a b

-- a Map's and a Set's key
count :: [Color] -> [(Color, Int)]
count cs = Map.toList (Map.fromListWith (+) [(c, 1) | c <- cs])

distinct :: [Shape] -> Int
distinct xs = length (Set.toList (Set.fromList xs))

look :: Color -> Maybe Int
look c = Map.lookup c (Map.fromList [(Red, 1), (Blue, 3)])

sets :: [Int] -> [Int] -> Ordering
sets xs ys = compare (Set.fromList xs) (Set.fromList ys)

maps :: [(Int, Bool)] -> [(Int, Bool)] -> Ordering
maps xs ys = compare (Map.fromList xs) (Map.fromList ys)
