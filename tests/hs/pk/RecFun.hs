module RecFun where

import Numeric.Natural (Natural)

-- functions as values

mapL :: (a -> b) -> [a] -> [b]
mapL f xs = case xs of
  [] -> []
  y : ys -> f y : mapL f ys

addAll :: Natural -> [Natural] -> [Natural]
addAll n xs = mapL (\x -> x + n) xs

foldrL :: (a -> b -> b) -> b -> [a] -> b
foldrL f z xs = case xs of
  [] -> z
  y : ys -> f y (foldrL f z ys)

applyAll :: Natural -> [Natural]
applyAll n = mapL (\f -> f n) [\x -> x + x, \x -> x + 1, \x -> x `div` n]

twice :: (a -> a) -> a -> a
twice f x = f (f x)

twiceTwice :: Natural -> Natural
twiceTwice n = twice (twice (\x -> x + n)) n

foldlL :: (b -> a -> b) -> b -> [a] -> b
foldlL f z xs = foldrL (\x k acc -> k (f acc x)) id xs z

minusAll :: Natural -> [Natural] -> Natural
minusAll n xs = foldlL (\a b -> a - b) n xs

factK :: Natural -> (Natural -> Natural) -> Natural
factK n k = if n < 1 then k 1 else factK (n - 1) (\v -> k (n * v))

fact :: Natural -> Natural
fact n = factK n id

-- a dictionary as a value, and as a class
data Mon a = Mon a (a -> a -> a)

mconcatD :: Mon a -> [a] -> a
mconcatD (Mon z op) xs = foldrL op z xs

sumD :: Mon Natural
sumD = Mon 0 (+)

appendD :: Mon [a]
appendD = Mon [] (++)

sumConcat :: [[Natural]] -> (Natural, [Natural])
sumConcat xss = let xs = mconcatD appendD xss in (mconcatD sumD xs, xs)

class Mo a where
  neutral :: a
  oper :: a -> a -> a

instance Mo Bool where
  neutral = True
  oper = (&&)

newtype Sum' = Sum' Natural

instance Mo Sum' where
  neutral = Sum' 0
  oper (Sum' a) (Sum' b) = Sum' (a + b)

mconcatC :: Mo a => [a] -> a
mconcatC = foldrL oper neutral

sumC :: [Natural] -> Natural
sumC xs = case mconcatC (mapL Sum' xs) of Sum' n -> n

allC :: [Bool] -> Bool
allC = mconcatC
