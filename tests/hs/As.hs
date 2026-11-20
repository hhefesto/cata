{-# LANGUAGE LambdaCase #-}
module As where

-- cata's as-patterns: x@p in clauses, case alternatives and lambdas, under
-- constructors, tuples and lists, with wildcards and literals under them,
-- one inside another

data Shape = Dot | Seg Int Int | Pair Shape Shape
  deriving (Eq, Show)

mkShape :: [Int] -> Shape
mkShape [] = Dot
mkShape [x] = Seg x (x * 2)
mkShape (x : xs) = Pair (Seg x x) (mkShape xs)

-- a clause's x@(C ..) with a wildcard under it
widen :: Shape -> Shape
widen s@(Seg _ b) = if b > 3 then s else Seg b b
widen (Pair a b) = Pair (widen a) (widen b)
widen d = d

widenList :: [Int] -> Shape
widenList xs = widen (mkShape xs)

-- one as-pattern inside another, and the outer one's variable twice
dupLeft :: Shape -> [Shape]
dupLeft p@(Pair l@(Seg _ _) _) = [p, l, l]
dupLeft p = [p]

dupLeftList :: [Int] -> [Shape]
dupLeftList xs = dupLeft (mkShape xs)

-- in a list, x@(y : _)
heads :: [[Int]] -> [[Int]]
heads xs = [ l | l@(y : _) <- xs, y > 0 ]

firstTwo :: [Int] -> [Int]
firstTwo all'@(a : b : _) = if a > b then all' else [a, b]
firstTwo other = other

-- in a case alternative, a tuple and a literal under it
pick :: [Int] -> (Int, Int)
pick xs = case (length xs, sum xs) of
  t@(0, _) -> t
  t@(_, s) | s > 10 -> (s, s)
           | otherwise -> t

-- in a \case
tags :: [Maybe Int] -> [Maybe Int]
tags = map (\case
  m@(Just 0) -> m
  Just n -> Just (n + 1)
  Nothing -> Nothing)

-- a character literal under one
quote :: String -> String
quote s@('"' : _) = s
quote s = '"' : s ++ "\""
