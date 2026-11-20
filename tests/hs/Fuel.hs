module Fuel where

-- how many times n halves before it is 0 (the argument shrinks by div)
halvings :: Int -> Int
halvings n = if n <= 0 then 0 else 1 + halvings (n `div` 2)

-- Collatz's steps to 1 (no measure at all: 3n+1 grows)
collatz :: Int -> Int
collatz n
  | n <= 1 = 0
  | even n = 1 + collatz (n `div` 2)
  | otherwise = 1 + collatz (3 * n + 1)

-- base-10 digits, most significant first
digits :: Int -> [Int]
digits n
  | n < 10 = [n]
  | otherwise = digits (n `div` 10) ++ [n `mod` 10]

-- Euclid's gcd (the second argument shrinks by mod)
gcd' :: Int -> Int -> Int
gcd' a 0 = a
gcd' a b = gcd' b (a `mod` b)

-- merge of two sorted lists (one list or the other shrinks)
merge :: [Int] -> [Int] -> [Int]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- the run of a list's equal neighbours (a list rebuilt before recursing)
runs :: [Int] -> [Int]
runs [] = []
runs [x] = [1]
runs (x:y:zs)
  | x == y = bump (runs (y:zs))
  | otherwise = 1 : runs (y:zs)
  where
    bump :: [Int] -> [Int]
    bump (k:ks) = (k + 1) : ks
    bump [] = [1]

-- a binary tree built by splitting a range (the range shrinks)
data Tree = Leaf | Node Tree Int Tree

build :: Int -> Int -> Tree
build lo hi
  | lo > hi = Leaf
  | otherwise = let mid = (lo + hi) `div` 2 in Node (build lo (mid - 1)) mid (build (mid + 1) hi)

inorder :: Tree -> [Int]
inorder Leaf = []
inorder (Node l x r) = inorder l ++ [x] ++ inorder r

range :: Int -> Int -> [Int]
range lo hi = inorder (build lo hi)

-- mutual: even and odd
isEven :: Int -> Bool
isEven n = if n <= 0 then True else isOdd (n - 1)

isOdd :: Int -> Bool
isOdd n = if n <= 0 then False else isEven (n - 1)

-- mutual through a list: a rose tree's size
data Rose = Rose Int [Rose]

sizeR :: Rose -> Int
sizeR (Rose _ ks) = 1 + sizeF ks

sizeF :: [Rose] -> Int
sizeF [] = 0
sizeF (r:rs) = sizeR r + sizeF rs

-- mutual with different answers: an expression's text, its arguments' texts
data E = Lit Int | Add E E | Call String [E]

render :: E -> String
render (Lit n) = show n
render (Add a b) = render a ++ " + " ++ render b
render (Call f es) = f ++ "(" ++ joinC (renderAll es) ++ ")"

renderAll :: [E] -> [String]
renderAll [] = []
renderAll (e:es) = render e : renderAll es

joinC :: [String] -> String
joinC [] = ""
joinC [s] = s
joinC (s:ss) = s ++ ", " ++ joinC ss

sampleR :: Rose
sampleR = Rose 1 [Rose 2 [], Rose 3 [Rose 4 []]]

sizeSample :: Int
sizeSample = sizeR sampleR

renderSample :: String
renderSample = render (Call "f" [Lit 1, Add (Lit 2) (Call "g" [])])
