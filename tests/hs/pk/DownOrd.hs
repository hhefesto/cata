-- base's Down: sorts the other way round (Eval.IC's renderICMeter)
module DownOrd where

import Data.List (sortBy, sortOn)
import Data.Ord (Down (..), comparing)
import qualified Data.Map as Map

rowsDown :: Map.Map Char Int -> [String]
rowsDown m = [ name : ' ' : show n | (name, n) <- sortOn (Down . snd) (Map.toList m) ]

sortDown :: [Int] -> [Int]
sortDown = sortBy (comparing Down)

exRows :: [Int] -> [String]
exRows xs = rowsDown (Map.fromList (zip "abcdefgh" xs))
