module FunArg where

-- cata's rule 15 test: a known function argument

-- a def that runs its function argument again
twice :: (Int -> Int) -> Int -> Int
twice f x = f (f x)

-- a section that names a local
useTwice :: Int -> Int
useTwice n = twice (+ n) 1

useTwiceL :: [Int] -> Int
useTwiceL xs = sum (map useTwice xs)

data T = L Int | N [T]

-- recursion through a function argument
mapT :: (T -> Int) -> [T] -> [Int]
mapT _ [] = []
mapT f (t : ts) = f t : mapT f ts

sumT :: T -> Int
sumT (L n) = n
sumT (N ts) = sum (mapT sumT ts)

mkT :: [Int] -> T
mkT [] = N []
mkT (x : xs) = if x > 0 then N [L x, mkT xs] else N [mkT xs]

sumTs :: [Int] -> Int
sumTs xs = sumT (mkT xs)

-- a closure that grows: copies stop
go :: ([Int] -> [Int]) -> [Int] -> [Int]
go f [] = f []
go f (x : xs) = go (f . (x :)) xs

rev :: [Int] -> [Int]
rev = go id

-- a lambda naming two locals
scale :: Int -> Int -> [Int] -> [Int]
scale a b xs = mapI (\x -> a * x + b) xs

mapI :: (Int -> Int) -> [Int] -> [Int]
mapI _ [] = []
mapI f (x : xs) = f x : mapI f xs
