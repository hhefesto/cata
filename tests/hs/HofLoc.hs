module HofLoc where

-- A list function's lambda over run-time locals (Spec's sp.hf: the
-- recursion it is, a local function, lifted with its locals): a parameter,
-- a pattern's or a let's variable, nested, and the composites that call
-- such a def at a run-time value; list comprehensions over an earlier
-- generator's variable; as-patterns in a module alone.

addAll :: Int -> [Int] -> [Int]
addAll n xs = map (\x -> x + n) xs

over :: Int -> [Int] -> [Int]
over n = filter (\x -> x > n)

total :: Int -> [Int] -> Int
total n xs = foldr (\x acc -> x + n + acc) 0 xs

-- the accumulator used twice, and not at all
twice :: Int -> [Int] -> Int
twice n xs = foldr (\x acc -> if x > n then acc + acc else acc + 1) 1 xs

lastBig :: Int -> [Int] -> Int
lastBig n xs = foldl (\acc x -> if x > n then x else acc) 0 xs

firstBig :: Int -> [Int] -> Maybe Int
firstBig n xs = foldr (\x acc -> if x > n then Just x else acc) Nothing xs

hasAbove :: Int -> [Int] -> Bool
hasAbove n xs = any (\x -> x > n) xs

allAbove :: Int -> [Int] -> Bool
allAbove n xs = all (\x -> x > n) xs

spread :: Int -> [Int] -> [Int]
spread n xs = concatMap (\x -> [x, n]) xs

upTo, from :: Int -> [Int] -> [Int]
upTo n xs = takeWhile (\x -> x < n) xs
from n xs = dropWhile (\x -> x < n) xs

pairUp :: Int -> [Int] -> [Int] -> [Int]
pairUp n xs ys = zipWith (\x y -> x + y + n) xs ys

tagged :: [(Int, Bool)] -> Int -> [Int]
tagged ps n = map (\(a, b) -> if b then a + n else a) ps

patLocal :: Maybe Int -> [Int] -> [Int]
patLocal (Just k) xs = map (\x -> x + k) xs
patLocal Nothing xs = xs

letLocal :: Int -> [Int] -> [Int]
letLocal n xs = let m = n + 2 in filter (\x -> x < m) xs

nested :: [Int] -> [Int] -> [[Int]]
nested xs ys = map (\x -> map (\y -> x + y) ys) xs

-- composites: the def called at a run-time value, under a lambda too
shift :: Int -> [Int] -> [Int]
shift x ys = addAll (x + 1) ys

each :: [Int] -> [Int] -> [[Int]]
each xs ys = map (\x -> addAll x ys) xs

sums :: [Int] -> [Int] -> [Int]
sums ns xs = map (\n -> total n xs) ns

-- list comprehensions
cart :: [Int] -> [Bool] -> [(Int, Bool)]
cart xs ys = [(x, y) | x <- xs, y <- ys]

tri :: Int -> [(Int, Int)]
tri n = [(a, b) | a <- [0 .. n], b <- [a .. n], a + b > 1]

-- as-patterns
grow :: [Int] -> [Int]
grow all'@(x : _) = x : all'
grow [] = []
