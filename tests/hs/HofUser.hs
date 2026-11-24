module HofUser where

-- A module's own function that is given a function: what it passes it may
-- be used more than once there (Bend's +, fd.tm).

myMap :: (a -> b) -> [a] -> [b]
myMap f [] = []
myMap f (x : xs) = f x : myMap f xs

myFold :: (a -> b -> b) -> b -> [a] -> b
myFold f z [] = z
myFold f z (x : xs) = f x (myFold f z xs)

myFoldl :: (b -> a -> b) -> b -> [a] -> b
myFoldl f z [] = z
myFoldl f z (x : xs) = myFoldl f (f z x) xs

myZip :: (a -> b -> c) -> [a] -> [b] -> [c]
myZip f (x : xs) (y : ys) = f x y : myZip f xs ys
myZip f _ _ = []

myMay :: (a -> b) -> Maybe a -> Maybe b
myMay f (Just x) = Just (f x)
myMay f Nothing = Nothing

times :: Int -> (a -> a) -> a -> a
times n f x = if n == 0 then x else f x

data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq, Show)

tmap :: (a -> b) -> Tree a -> Tree b
tmap f Leaf = Leaf
tmap f (Node l x r) = Node (tmap f l) (f x) (tmap f r)

tfold :: (b -> a -> b -> b) -> b -> Tree a -> b
tfold f z Leaf = z
tfold f z (Node l x r) = f (tfold f z l) x (tfold f z r)

squares :: [Int] -> [Int]
squares xs = myMap (\x -> x * x + x) xs

total :: [Int] -> Int
total xs = myFold (\x acc -> if x > acc then x + acc else acc) 0 xs

best :: [Int] -> Int
best xs = myFoldl (\acc x -> if x > acc then x else acc) 0 xs

prods :: [Int] -> [Int] -> [Int]
prods xs ys = myZip (\x y -> x * x + y * y + x * y) xs ys

may :: Maybe Int -> Maybe Int
may m = myMay (\x -> x * x) m

tsq :: Tree Int -> Tree Int
tsq t = tmap (\x -> x * x) t

tsum :: Tree Int -> Int
tsum t = tfold (\l x r -> if l > r then l + x else r + r) 0 t

twice :: Int -> Int
twice n = times n (\x -> x * x) 3
