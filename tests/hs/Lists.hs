module Lists where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Bifunctor (first, second, bimap)
import Data.List (sortOn, nub, intercalate)
import Data.Maybe (catMaybes)

emptySet :: Set.Set Int
emptySet = mempty

emptyMap :: Map.Map Int Bool
emptyMap = mempty

noKeys :: Map.Map Int Bool -> Bool
noKeys m = m == mempty

bumpLeft :: Either Int Bool -> Either Int Bool
bumpLeft = first (+ 1)

flipRight :: Either Int Bool -> Either Int Bool
flipRight = second not

bumpFst :: (Int, Bool) -> (Int, Bool)
bumpFst = first (* 2)

flipSnd :: (Int, Bool) -> (Int, Bool)
flipSnd = second not

both :: (Int, Bool) -> (Int, Bool)
both = bimap (+ 1) not

lengths :: [(String, Int)] -> [(Int, Int)]
lengths = fmap (first length)

noneSet :: Set.Set Int -> Bool
noneSet = null

bumpVals :: Map.Map Int Int -> Map.Map Int Int
bumpVals = fmap (+ 1)

indexed :: [Bool] -> [(Int, Bool)]
indexed = zip [0 ..]

indexedR :: [Bool] -> [(Bool, Int)]
indexedR xs = zip xs [1 ..]

labels :: [Bool] -> [Int]
labels = zipWith (\i b -> if b then i else negate i) [0 ..]

labelsR :: [Bool] -> [Int]
labelsR xs = zipWith (\b i -> if b then i else 0) xs [5 ..]

anySet :: Set.Set Int -> Bool
anySet = any (> 3)

sumMap :: Map.Map Bool Int -> Int
sumMap = foldr (+) 0

lenSet :: Set.Set Char -> Int
lenSet = length

pairsUp :: [(Int, Bool)] -> ([Int], [Bool])
pairsUp = unzip

findBig :: [Int] -> Maybe Int
findBig = foldr (\x r -> if x > 10 then Just x else r) Nothing

sorted :: [(Int, Char)] -> [(Int, Char)]
sorted = sortOn snd

flipped :: Int -> Int -> Int
flipped = flip (-)

uniq :: [Int] -> [Int]
uniq = nub

text :: String -> [String]
text s = lines s ++ words s

joinUp :: [String] -> String
joinUp = intercalate ", "

firsts :: [(Int, Bool)] -> [Int]
firsts = map fst

look :: Int -> [(Int, String)] -> Maybe String
look = lookup

keep :: [Maybe Int] -> [Int]
keep = catMaybes
