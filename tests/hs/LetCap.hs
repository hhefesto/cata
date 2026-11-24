module LetCap where

-- a local function, or a case, in a value bound beside others: the lifted
-- def takes the ones it uses (Fold's fd.bindenv), as it takes the parameters

sums :: [Int] -> [String]
sums xs = map (\(n, k) -> show n ++ show (k + width)) counts
  where
    counts = zip xs (map (* 2) xs)
    width = sum (map (\p -> fst p + length xs) counts)

inCase :: [Int] -> [Int]
inCase xs = xs ++ [width]
  where
    counts = zip xs xs
    width = case counts of
      [] -> length xs
      (p : _) -> let g n = n + length counts in g (fst p)

inLet :: [Int] -> [Int]
inLet xs = xs ++ [width]
  where
    counts = zip xs xs
    width = let g n = n + length xs in g (length counts)

inLoop :: [Int] -> [Int]
inLoop xs = xs ++ [width]
  where
    counts = zip xs xs
    width = let go [] = 0
                go (y : ys) = y + length xs + go ys
             in go (map fst counts)

rows :: [Int] -> [String]
rows xs = map render counts
  where
    counts = zip xs (map (* 2) xs)
    render (n, k) = place n ++ replicate width ' ' ++ show k
    place n = show (n + length xs)
    width = maximum (0 : map (length . place . fst) counts)

roots :: [Int] -> [Int]
roots xs = case kept of
  [] -> failures
  ks -> ks
  where
    failures = map (+ 1) xs
    kept = case filter big failures of
      [] -> take 1 failures
      r -> r
    big n = n > 3

-- a lifted def's parameters are not named as what it captures (x0 here is
-- the fold's own name for a first parameter)
padded :: Int -> Int -> [Int] -> [Int] -> [Int]
padded x0 y0 xs ys = go xs ys
  where
    go [] [] = []
    go as [] = map (+ y0) as
    go [] bs = map (\b -> x0 + b) bs
    go (a : as) (b : bs) = (a * b + x0) : go as bs

hides :: Int -> [Int] -> Int
hides a xs = go xs 0
  where
    go [] n = n + a
    go [b] a' = a + b + a'
    go (b : bs) a' = go bs (a' + b)
