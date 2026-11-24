module LiftPoly where

-- recursion through a lifted def at a type variable: the group's type
-- variables are templates (Fold's fd.mu.er)

halves :: [a] -> ([a], [a])
halves xs = case xs of
  [] -> ([], [])
  [x] -> ([x], [])
  x : y : zs -> case halves zs of
    (as, bs) -> (x : as, y : bs)

merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
merge le xs ys = case (xs, ys) of
  ([], _) -> ys
  (_, []) -> xs
  (a : as, b : bs) -> if le a b then a : merge le as ys else b : merge le xs bs

takeN :: Int -> [a] -> [a]
takeN n xs = case (n, xs) of
  (0, _) -> []
  (_, []) -> []
  (_, y : ys) -> y : takeN (pred' n) ys

pred' :: Int -> Int
pred' 0 = 0
pred' n = length (drop 1 (replicate n ()))

weave :: [a] -> [a] -> [a]
weave xs ys = case xs of
  [] -> ys
  a : as -> a : weave ys as

chunk :: Int -> [a] -> [[a]]
chunk n xs = case xs of
  [] -> []
  _ -> takeN n xs : chunk n (drop (max 1 n) xs)

weaves :: [Int] -> [Int] -> [Int]
weaves = weave

mergeInts :: [Int] -> [Int] -> [Int]
mergeInts = merge (<=)

chunks :: Int -> String -> [String]
chunks = chunk
