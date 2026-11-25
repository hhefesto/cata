-- A local value that may fail, used where Haskell may never force it: only
-- inside a mapped function (Certificate's width), in the right side of &&,
-- in an if's branch; the tail zip never forces
module LazyLet where

rows :: [(String, Int)] -> [String]
rows xs = fmap render xs
  where
    width = maximum (fmap (length . fst) xs)
    render (n, k) = n ++ replicate (width + 1 - length n) '.' ++ show k

shift :: [Int] -> [Int]
shift xs = let m = minimum xs in map (\x -> x - m) xs

incr :: [Int] -> Bool
incr xs = all (\(a, b) -> a <= b) (zip xs (tail xs))

diffs :: [Int] -> [Int]
diffs xs = zipWith (\a b -> b - a) xs (tail xs)

clean :: [Int] -> Maybe [Int]
clean ds
  | n == 3 = Just ds
  | n == 4 && head ds == 1 = Just (tail ds)
  | null ds || head ds > 5 = Nothing
  | otherwise = Just []
  where n = length ds

pick :: Int -> [Int] -> Int
pick k xs = let h = head xs in if k > 0 then h + k else if k > -2 then 0 else h
