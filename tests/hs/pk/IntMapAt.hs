module IntMapAt where

import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Strict as IntMapS

-- containers' IntMap (!) at a missing key: IntMap's own error text
atOne :: Int -> Int -> Int
atOne n k = IntMap.fromList [(0, n), (1, 2 * n)] IntMap.! k

atBoth :: [Int] -> Int -> (Int, Bool)
atBoth xs k = (IntMapS.fromList (zip [0 ..] xs) IntMapS.! k, (IntMap.fromList [(0, True)] IntMap.! 0) && k > 0)

atAll :: [Int] -> [Int]
atAll ks = map (\k -> IntMap.fromList [(0, 10), (1, 20), (2, 30)] IntMap.! k) ks
