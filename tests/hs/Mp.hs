module Mp where

-- cata's Data.Map rule: Map, IntMap, Set and IntSet as HsPrelude's ordered
-- HsMap and HsSet, compare at the key a template

import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Strict as MapS
import Data.Set (Set)
import qualified Data.Set as Set

build :: [(Int, Int)] -> Map Int Int
build = Map.fromList

roundTrip :: [(Int, Int)] -> [(Int, Int)]
roundTrip xs = Map.toList (build xs)

counts :: [Int] -> [(Int, Int)]
counts xs = Map.toList (Map.fromListWith (+) [(x, 1) | x <- xs])

counts' :: String -> [(Char, Int)]
counts' s = Map.toList (MapS.fromListWith (+) (map (\c -> (c, 1)) s))

look :: Int -> [(Int, Int)] -> Maybe Int
look k xs = Map.lookup k (build xs)

lookDef :: Int -> [(Int, Int)] -> Int
lookDef k xs = Map.findWithDefault 0 k (build xs)

has :: Int -> [(Int, Int)] -> Bool
has k xs = Map.member k (build xs)

bumped :: Int -> [(Int, Int)] -> [(Int, Int)]
bumped k xs = Map.toList (Map.adjust (+ 10) k (Map.insertWith (+) k 1 (build xs)))

dropped :: Int -> [(Int, Int)] -> [Int]
dropped k xs = Map.keys (Map.delete k (build xs))

merged :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
merged a b = Map.toList (Map.unionWith (+) (build a) (build b))

leftWins :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
leftWins a b = Map.toList (Map.union (build a) (build b))

semi :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
semi a b = Map.toList (build a <> build b)

total :: [(Int, Int)] -> Int
total xs = Map.foldr (+) 0 (build xs)

bigOnes :: [(Int, Int)] -> [Int]
bigOnes xs = Map.elems (Map.filter (> 1) (build xs))

sizes :: [(Int, Int)] -> (Int, Bool)
sizes xs = (Map.size (build xs), Map.null (build xs))

doubled :: [(Int, Int)] -> [(Int, Int)]
doubled xs = Map.toList (Map.map (* 2) (build xs))

sameMap :: [(Int, Int)] -> [(Int, Int)] -> Bool
sameMap a b = build a == build b

byName :: [(String, Int)] -> Maybe Int
byName xs = Map.lookup "ab" (Map.fromList xs)

-- IntMap
im :: [(Int, Int)] -> [(Int, Int)]
im xs = IntMap.toList (IntMap.insert 1 7 (IntMap.fromList xs))

imDiff :: [(Int, Int)] -> [(Int, Int)] -> [Int]
imDiff a b = IntMap.keys (IntMap.difference (IntMap.fromList a) (IntMap.fromList b))

-- Set, IntSet
uniq :: [Int] -> [Int]
uniq xs = Set.toList (Set.fromList xs)

inSet :: Int -> [Int] -> Bool
inSet x xs = Set.member x (Set.insert 2 (Set.fromList xs))

setOps :: [Int] -> [Int] -> ([Int], [Int])
setOps a b = (Set.toList (Set.union (Set.fromList a) (Set.fromList b)), Set.toList (Set.difference (Set.fromList a) (Set.fromList b)))

keySet :: [(Int, Int)] -> [Int]
keySet xs = Set.toList (Map.keysSet (build xs))

intSet :: [Int] -> [Int]
intSet xs = IntSet.toList (IntSet.delete 1 (IntSet.fromList xs))

charSet :: String -> String
charSet s = Set.toList (Set.fromList s)
