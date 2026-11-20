module Lifted where

-- a where-function that calls the def it is in
total :: [Int] -> Int
total [] = 0
total (x : xs) = go xs
  where go ys = x + total ys

-- a lambda that calls its def, through a case on a computed value
depthOf :: [[Int]] -> Int
depthOf [] = 0
depthOf (l : ls) = case l of
  [] -> depthOf ls
  _ -> 1 + depthOf ls
