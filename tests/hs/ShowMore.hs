module ShowMore where

-- Show at (), at pairs, at Data.Map's maps and at Data.Set's sets, as
-- telomare shows them (Size's sizeTermM: a pair, a map in an error's
-- text; InputRestrictions, a set; the () of a functor's annotation),
-- inside a list, a Maybe and each other, at precedence 0 and 11.

import qualified Data.Map as Map
import qualified Data.Set as Set

unitText :: () -> String
unitText u = show u

pairText :: Int -> Bool -> String
pairText n b = show (n, b)

pairsText :: [(Int, Char)] -> String
pairsText ps = show ps

nestedPair :: Int -> String
nestedPair n = show ((n, n + 1), Just n)

mapText :: [(Int, String)] -> String
mapText kvs = show (Map.fromList kvs)

setText :: [Int] -> String
setText xs = show (Set.fromList xs)

-- a map inside a Just: its showsPrec at 11, so in parentheses
justMap :: [(Int, Int)] -> String
justMap kvs = show (Just (Map.fromList kvs))

-- a set of pairs, a map to sets
setOfPairs :: [(Int, Int)] -> String
setOfPairs ps = show (Set.fromList ps)

mapOfSets :: [(Int, [Int])] -> String
mapOfSets kvs = show (Map.fromList [(k, Set.fromList vs) | (k, vs) <- kvs])

showsAt :: Int -> (Int, Int) -> String
showsAt d p = showsPrec d p ""
