{-# LANGUAGE ScopedTypeVariables #-}
-- a map tied through itself, its step using functions it was given
module KnotClo where

import Data.Map (Map)
import qualified Data.Map as Map

sizes :: (Int -> Int) -> (Int -> Bool) -> Map Int [Int] -> Map Int Int
sizes links erased d = images
  where
    images = Map.map image d
    image xs = sum [ if erased x then links x else 1 + Map.findWithDefault 0 x images | x <- xs ]

exSizes :: Int -> Map Int Int
exSizes n = sizes (+ n) (> 3) (Map.fromList [(1, [2, 3]), (2, [4, 5]), (3, [6, 2])])
