module GuardFall where

-- Guards that all fail: Haskell goes on to the next clause (Fold's fd.ft:
-- the rest of the clauses, read at what the clause's patterns say, a def
-- of its variables).  Telomare's shapes: EAL's meetShape (variables, then
-- constructors), IC's rule and Resolve's debruijinize (constructors, a
-- guard, the same constructor again), a case's alternatives.

data Shape = Leaf | Node Shape Shape | Tip Int
  deriving (Eq, Show)

small :: Shape -> Bool
small Leaf = True
small (Tip _) = True
small _ = False

-- variables first: the whole rest is the fall's
meet :: Shape -> Shape -> Shape
meet a b
  | a == b = a
meet (Node a b) (Node c d) = Node (meet a c) (meet b d)
meet a b
  | small a && small b = Leaf
  | otherwise = Node a b

-- constructors, the same one again, a wildcard the later clause splits
pick :: [Int] -> Int
pick (x : _)
  | x > 2 = x
pick (_ : y : _) = y + 10
pick _ = 100

-- no clause can match after the guard but the last
count :: Maybe Int -> Int
count Nothing = 0
count (Just n)
  | n > 1 = n
count (Just _) = 50

-- literals
lit :: Int -> Int -> Int
lit 0 m
  | m > 1 = 7
lit 0 1 = 8
lit n m = n + m

-- three falls in a row
stairs :: Int -> Int -> Int
stairs a b
  | a > 2 = 1
stairs a b
  | b > 2 = 2
stairs 1 b
  | b == 1 = 3
stairs a b = a + b + 10

-- a variable of a later clause names a part the first one took apart
whole :: [Int] -> [Int]
whole (x : xs)
  | x == 0 = xs
whole ys = 9 : ys

-- a pair, and a where the fall is under
pairs :: (Int, Bool) -> [Int] -> Int
pairs (n, True) xs
  | m > 1 = m + n
  where
    m = length xs
pairs (n, b) [] = if b then n else 0
pairs (n, _) (x : _) = n + x

-- a case's alternatives, in a function that has locals
alt :: Int -> Maybe Int -> Int
alt n m = case m of
  Just k
    | k > n -> k
  Just k -> n + k
  Nothing -> n

-- a local function's
runs :: [Int] -> [Int]
runs = go 0
  where
    go :: Int -> [Int] -> [Int]
    go n (x : xs)
      | x == n = go n xs
    go n (x : xs) = x : go x xs
    go n [] = [n]

-- a string's
word :: String -> Int
word ('a' : cs)
  | length cs == 1 = 1
word "ab" = 2
word ('a' : _) = 3
word _ = 4

-- polymorphic, and a recursion through the fall
dedup :: Eq a => [a] -> [a]
dedup (x : y : zs)
  | x == y = dedup (y : zs)
dedup (x : xs) = x : dedup xs
dedup [] = []

-- GHC's PatternMatchFail where the last clause's guards fail: out
part :: Int -> Int
part n
  | n > 1 = n
