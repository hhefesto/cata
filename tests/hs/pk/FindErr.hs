module FindErr where

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

-- a default that fails is forced only where the key is missing
renamed :: [Int] -> Int -> Int
renamed outer n
  | n == 0 = 0
  | otherwise = Map.findWithDefault (error ("lost variable " ++ show n)) (n - 1) positions
  where positions = Map.fromList (zip outer [1 ..])

renamedI :: [Int] -> Int -> Int
renamedI outer n = IntMap.findWithDefault (error "lost") n (IntMap.fromList (zip outer [1 ..]))

orHead :: [Int] -> Maybe Int -> Int
orHead xs = fromMaybe (head xs)

orHead2 :: [Int] -> Maybe Int -> Int
orHead2 xs m = fromMaybe (maximum xs) m + 1

safe :: Int -> Maybe Int -> Int
safe d m = fromMaybe (d + 1) m
