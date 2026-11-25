-- partial steps of foldl and foldr over run-time locals, written with an
-- accumulator pair and a local step (EAL's eliminate, dropArtificials,
-- dualSolve's addRow)
module PartFold where

import qualified Data.Map as Map
import qualified Data.IntMap.Strict as IntMap

data Tab = Tab (IntMap.IntMap Int) Int
  deriving (Eq, Show)

pivot :: Int -> Int -> Tab -> Tab
pivot r c (Tab rows n) = Tab (IntMap.insert r (rows IntMap.! c) rows) (n + 1)

dropAll :: Int -> Tab -> [(Int, Int)] -> Tab
dropAll base tab0 xs = foldr step tab0 (filter (\(a, _) -> a >= base) xs)
  where
    step (a, b) tab@(Tab rows n)
      | IntMap.member a rows = pivot a b tab
      | n > 4 = error "dropAll: too many"
      | otherwise = Tab (IntMap.insert b a rows) n

exDrop :: Int -> [(Int, Int)] -> ([(Int, Int)], Int)
exDrop base xs = case dropAll base (Tab (IntMap.fromList [(1, 2), (base, 3)]) 0) xs of
  Tab rows n -> (IntMap.toList rows, n)

addRows :: Map.Map Int Int -> Int -> Tab -> [(Int, Int)] -> Tab
addRows colOf base tab0 rs = foldl addRow tab0 rs
  where
    addRow (Tab rows n) (i, v) =
      let c = colOf Map.! i
          (k, m) = foldl (sub c) (v, n) (IntMap.toList rows)
      in Tab (IntMap.insert (base + i) k rows) (n + m)
    sub c (acc, t) (j, w) = if j == c then (acc + w, t + div w (acc - 2)) else (acc, t)

exRows :: Int -> [(Int, Int)] -> ([(Int, Int)], Int)
exRows base rs = case addRows (Map.fromList [(0, 1), (1, base), (2, 5)]) base (Tab (IntMap.fromList [(1, base), (5, 2)]) 1) rs of
  Tab rows n -> (IntMap.toList rows, n)

-- a partial function at Map.unionWithKey (Resolve's DeferMap)
newtype DM = DM (Map.Map Int (Int, String))

instance Semigroup DM where
  DM a <> DM b = DM $ Map.unionWithKey f a b where
    f k x@(_, s) (_, t) = if s /= t then error ("collision " ++ show k) else x

exDM :: Int -> Int -> String -> String -> [(Int, (Int, String))]
exDM a b s t = case DM (Map.fromList [(a, (1, s)), (2, (2, "q"))]) <> DM (Map.fromList [(b, (3, t)), (2, (4, "q"))]) of DM m -> Map.toList m
