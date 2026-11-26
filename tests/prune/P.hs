module P where

-- A record whose run reads one field: the other two, and what builds
-- them, are never evaluated by GHC's run of `run`.
data R = R { used :: Int, unused :: Int, alsoUnused :: [Int] }

expensive :: Int -> Int
expensive n = sum [1 .. n]

mk :: Int -> Int -> R
mk a b = R { used = a, unused = cost, alsoUnused = helper b }
  where helper x = replicate x x
        cost = expensive b

-- y is never used
combine :: Int -> Int -> Int -> Int
combine x y z = x + z

-- a positional record, its second field never read
data Q = Q Int Int

qfst :: Q -> Int
qfst (Q a _) = a

run :: Int -> Int
run n = used (mk n n) + combine 1 (expensive n) 2 + qfst (Q n (expensive n))
