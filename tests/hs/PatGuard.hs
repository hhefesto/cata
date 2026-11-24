module PatGuard where

-- Pattern guards (Fold's fd.pg: a case on the guard's value, lifted, the
-- guards after it in the pattern's branch; Spec's sp.ftw.binds writes the
-- pattern's type): alone, with conditions before and after, several in a
-- row, over the rest of the chain, falling through to the next clause.

data Cmd = Push Int | Pop | Jump Int Bool
  deriving (Eq, Show)

look :: Int -> [(Int, Int)] -> Maybe Int
look _ [] = Nothing
look k ((a, b) : t) = if a == k then Just b else look k t

one :: Int -> [(Int, Int)] -> Int
one k env
  | Just v <- look k env = v
  | otherwise = 100

two :: Int -> [(Int, Int)] -> Int
two k env
  | Just v <- look k env, v > 1 = v
  | Just v <- look (k + 1) env = v + 50
  | k == 2 = 200
  | otherwise = 100

chain :: Int -> [(Int, Int)] -> Int
chain k env
  | Just v <- look k env, Just w <- look v env = v + w
  | otherwise = 100

cond :: Int -> [Int] -> Int
cond n xs
  | n > 0, (x : _) <- xs = x + n
  | [] <- xs = 7
  | otherwise = n

own :: Cmd -> Int
own c
  | Push n <- c, n > 1 = n
  | Jump n True <- c = n + 10
  | otherwise = 3

-- to the next clause
next :: [Int] -> Maybe Int -> Int
next (x : _) m
  | Just v <- m, v > x = v
next [] m
  | Just v <- m = v + 10
next _ _ = 99

-- a case's alternative, a variable pattern, a tuple's
alts :: Maybe Int -> [Int] -> Int
alts m xs = case m of
  Just n
    | y <- n + 1, y > 2 -> y
    | (a, b) <- (n, length xs) -> a + b
  Nothing -> 0

-- a recursion under one
total :: [Cmd] -> Int
total [] = 0
total (c : cs)
  | Push n <- c = n + total cs
  | otherwise = total cs
