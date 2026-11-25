module Held where

import Data.Map (Map)
import qualified Data.Map as Map

-- a local value that may fail, used only in what runs again and again
-- (telomare's dualSolve: waitingAt): computed once, its error where it is read
looks :: [(Int, String)] -> [Int] -> [String]
looks ps ks = concatMap look ks
  where
    look k = if k < 0 then [] else [ w | Just w <- [Map.lookup k table] ]
    table = Map.map (++ first) (Map.fromList ps)
    first = snd (head ps)

loop :: [(Int, Int)] -> Int -> [Int] -> Either String [Int]
loop ps n xs = go n xs
  where
    cols = Map.fromList ps
    inv = Map.fromListWith (++) [ (cols Map.! k, [k]) | (k, _) <- ps, k /= 9 || Map.member 9 cols ]
    tops = maximum (map snd ps)
    go 0 ys = Right ys
    go m ys = if length ys > 50 then Left (show (length ys))
              else go (m - 1) ([ z | y <- ys, z <- Map.findWithDefault [] y inv ] ++ take 1 [ tops | m > 2 ])
