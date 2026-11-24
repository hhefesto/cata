module PartLet where

import qualified Data.Map as Map

-- a foldl whose step has lets of partial calls
type Rows = Map.Map Int (Map.Map Int Int, Int)

stepAll :: Rows -> [Int] -> (Rows, Int)
stepAll rows js = foldl step (rows, 0) js
  where
    step (rs, n) j =
      let (row, b) = rs Map.! j
          a = row Map.! 0
          b' = b - a * n
      in (Map.insert j (row, b') rs, n + a)

affected :: Rows -> Int -> [Int]
affected rows c = [j | j <- Map.keys rows, j /= 1, Map.member c (fst (rows Map.! j))]

combine :: Int -> Map.Map Int Int -> Map.Map Int Int -> Map.Map Int Int
combine a p row = Map.filter (/= 0) (Map.unionWith (+) row (Map.map (\v -> negate (a * v)) p))

pivot :: Int -> Int -> Rows -> Rows
pivot r c rows =
  let (prow, pb) = rows Map.! r
      p = prow Map.! c
      prow' = Map.map (`div` p) prow
      pb' = pb `div` p
      aff = affected rows c
      go rs j =
        let (row, b) = rs Map.! j
            a = row Map.! c
        in Map.insert j (combine a prow' row, b - a * pb') rs
      rows1 = foldl go rows aff
  in Map.insert r (prow', pb') rows1

-- a local recursion over an index
iter :: (Int -> Int) -> Int -> Int -> Int
iter f x n = iterate f x !! n

double :: Int -> Int
double n = iter (* 2) 1 n

-- foldr over a partial function's answers
sumAt :: Map.Map Int Int -> [Int] -> Int
sumAt m ks = foldr (\k acc -> (m Map.! k) + acc) 0 ks
