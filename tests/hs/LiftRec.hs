module LiftRec where

-- Recursion through a case, an if or a let lifted out of the def (Fold's
-- fd.cy): the call is made at the lifted def's call, a value where it is
-- one and shrinks, a thunk else; the def's recursion is then its own, with
-- no fuel where it is structural.

table :: [(Int, Int)]
table = [(0, 5), (2, 7)]

find' :: Int -> [(Int, Int)] -> Maybe Int
find' _ [] = Nothing
find' k ((a, b) : t) = if a == k then Just b else find' k t

-- one call in two branches
total :: [Int] -> Int
total [] = 0
total (x : xs) = case find' x table of
  Just y -> y + total xs
  Nothing -> total xs

-- two calls, one of them run
merge :: [Int] -> [Int] -> [Int]
merge [] ys = ys
merge xs [] = xs
merge (x : xs) (y : ys) = case compare x y of
  LT -> x : merge xs (y : ys)
  _ -> y : merge (x : xs) ys

data Tree = Leaf | Node Tree Int Tree
  deriving (Eq, Show)

member :: Int -> Tree -> Bool
member _ Leaf = False
member k (Node l x r) = case compare k x of
  LT -> member k l
  GT -> member k r
  EQ -> True

insert :: Int -> Tree -> Tree
insert k Leaf = Node Leaf k Leaf
insert k (Node l x r) = case compare k x of
  LT -> Node (insert k l) x r
  GT -> Node l x (insert k r)
  EQ -> Node l x r

-- the call's answer an error, unforced where the branch does not use it
parts :: [Int] -> Int
parts [] = 0
parts (x : xs) = case find' x table of
  Just y -> y
  Nothing -> x `div` parts xs

-- a foldr's step with a case on its accumulator's neighbour
steps :: Int -> [Int] -> Int
steps n xs = foldr (\x acc -> case find' (x + n) table of { Just y -> y + acc; Nothing -> acc }) 1 xs

-- a local recursion, a case's, a fuelled one
count :: Int -> [Int] -> Int
count n xs0 = go xs0 0
  where
    go [] acc = acc
    go (x : xs) acc = case find' x table of
      Just y -> if y > n then go xs (acc + 1) else go xs acc
      Nothing -> go xs acc

halve :: Int -> Int
halve n = case find' n [(1, 0), (0, 0)] of
  Just y -> y
  Nothing -> 1 + halve (n `div` 2)
