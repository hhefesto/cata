module PatBind where

-- Local pattern bindings (a tuple's parts named at once), as telomare
-- writes them: a let's (EAL's components: `(g, nodeFromVertex, _) =
-- Graph.graphFromEdges ..`), a where's (Levels' spine, Driver's
-- funWrapWith), a triple with a wildcard, a pair inside a pair, and one
-- whose parts feed a later binding of the same let.

-- the sum and the count of a list, at once
sumCount :: [Int] -> (Int, Int)
sumCount [] = (0, 0)
sumCount (x : xs) = let (s, n) = sumCount xs in (s + x, n + 1)

-- the mean's integral part, or 0 for none
mean :: [Int] -> Int
mean xs = if n == 0 then 0 else s `div` n
  where
    (s, n) = sumCount xs

-- a triple's first two, the third ignored
firstTwo :: Int -> Int
firstTwo k =
  let (a, b, _) = (k + 1, k * 2, k - 3)
  in a * b

-- a pair inside a pair
nested :: Int -> Int -> Int
nested p q =
  let ((a, b), c) = ((p, q), p + q)
  in a - b + c

-- a binding that uses the parts of the one before it
chained :: Int -> Int
chained k =
  let (a, b) = (k, k + 1)
      c = a * b
      (d, e) = (c + a, c - b)
  in d + e

-- the parts named in a guard's where
classify :: [Int] -> Int
classify xs
  | lo > hi = 0
  | lo == hi = 1
  | otherwise = 2
  where
    (lo, hi) = (length (filter (< 0) xs), length (filter (> 0) xs))
