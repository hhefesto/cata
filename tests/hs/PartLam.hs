module PartLam where

-- Partial calls inside a list function's lambda (the prelude's HsPt of it,
-- its function answering the Either), and partial defs written point-free
-- (Fold's fd.el: their lambda's variables their parameters).

divs :: [Int] -> [Int]
divs xs = map (\x -> 10 `div` x) xs

heads :: [[Int]] -> [Int]
heads xss = map head xss

folded :: [Int] -> Int
folded xs = foldr (\x acc -> (acc + 7) `mod` x) 3 xs

folded' :: [Int] -> Int
folded' xs = foldl (\acc x -> (acc + 7) `mod` x) 3 xs

kept :: [Int] -> [Int]
kept xs = filter (\x -> 6 `mod` x == 0) xs

some :: [Int] -> Bool
some xs = any (\x -> 4 `div` x == 2) xs

every :: [Int] -> Bool
every xs = all (\x -> 4 `div` x > 0) xs

zips :: [Int] -> [Int] -> [Int]
zips xs ys = zipWith (\a b -> a `div` b) xs ys

firsts :: [[Int]] -> Int
firsts xss = sum (map (\xs -> head xs + 1) xss)

-- point-free
first :: [Int] -> Int
first = head

isVowel :: Char -> Bool
isVowel c = c `elem` "aeiou"

vowelFirst :: String -> Bool
vowelFirst = isVowel . head

least :: [Int] -> Int
least = minimum

biggest :: [Int] -> Int
biggest = (+ 1) . maximum

useLeast :: [Int] -> Int
useLeast xs = least xs + first xs

rest :: [Int] -> [Int]
rest = tail . tail
