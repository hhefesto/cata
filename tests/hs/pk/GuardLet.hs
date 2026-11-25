-- a let among a clause's guards, which falls through to the next ones
module GuardLet where

verdict :: Int -> [Int] -> ([Int], Bool)
verdict k fs
  | all (> 0) fs
  , let runs = [ f * k | f <- fs ]
  , not (any (> 20) runs) = (runs, False)
  | otherwise = ([], True)

pick :: Int -> Maybe Int -> Int
pick n m
  | Just x <- m, let y = x + n, y > 3 = y
  | let z = n * 2, z > 10 = z
pick n Nothing = n
pick n (Just x) = n - x
