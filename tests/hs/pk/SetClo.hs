-- Set's filter and map at a function over a local (Machine's isUnbounded)
module SetClo where

import Data.Set (Set)
import qualified Data.Set as Set

isUnbounded :: Set Integer -> Integer -> Bool
isUnbounded s n = f s
  where
  f s'
    | null s' = True
    | Set.member n s' = False
    | otherwise = (f . Set.map (flip div 2 . pred)) $ Set.filter (>= n) s'

shifted :: Int -> Set Int -> Set Int
shifted k s = Set.map (\x -> x * k + 1) s

exUn :: [Integer] -> Integer -> Bool
exUn xs n = if isUnbounded (Set.fromList xs) n then n > 3 else n < 5

exShift :: Int -> [Int] -> [Int]
exShift k xs = Set.toList (shifted k (Set.fromList xs))
