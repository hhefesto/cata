module PartialFold where

-- Foldable's partial functions at a list, as telomare writes them:
-- maximum (EAL's inferEALLifted), minimum and minimumBy (EAL's simplex),
-- foldr1 (EAL's messageAborts), and maximumBy, foldl1; each written as a
-- failure value, GHC's message on the left.

import Data.List (maximumBy, minimumBy)
import Data.Ord (comparing)

-- the largest and the smallest
top :: [Int] -> Int
top xs = maximum xs

bottom :: [Int] -> Int
bottom xs = minimum xs

-- of two equal keys maximumBy keeps the later pair, minimumBy the earlier
latest :: [(Int, Int)] -> (Int, Int)
latest ps = maximumBy (comparing fst) ps

earliest :: [(Int, Int)] -> (Int, Int)
earliest ps = minimumBy (comparing fst) ps

-- right and left folds without a seed
spread :: [Int] -> Int
spread xs = foldr1 (-) xs

drift :: [Int] -> Int
drift xs = foldl1 (-) xs

-- two partial calls in lets: on an empty list GHC throws maximum's error
-- (its exceptions are imprecise: either is allowed), cata binds minimum
-- first; out on its law, by design (README, "Partial functions")
range :: [Int] -> Int
range xs = let hi = maximum xs; lo = minimum xs in hi - lo + hi * 0

-- a partial def called from another, in an argument
gap :: [Int] -> [Int] -> Int
gap xs ys = top xs - bottom ys

-- on a list of strings (Ord at a list)
longestName :: [String] -> String
longestName ns = maximum ns
