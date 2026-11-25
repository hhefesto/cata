-- two operators of one type, and two defs whose names differ by a prime or an
-- underscore, copied at the same types
module OpNames where

import Data.Foldable (traverse_)

newtype P = P (Int, Int) deriving Show

instance Eq P where
  P (a, b) == P (c, d) = a + b == c + d
  P (a, b) /= P (c, d) = a * b /= c * d

instance Semigroup P where
  P (a, b) <> P (c, d) = P (a + c, b * d)

put :: (Eq a, Semigroup a) => a -> a -> a
put a b = if a == b then a <> b else b

put' :: (Eq a, Semigroup a) => a -> a -> a
put' a b = if a /= b then b <> a else a

exPut :: Int -> Int -> Int -> Int
exPut a b c = case put (P (a, b)) (P (b, c)) of P (x, y) -> x + 10 * y

exPut' :: Int -> Int -> Int -> Int
exPut' a b c = case put' (P (a, b)) (P (b, c)) of P (x, y) -> x + 10 * y

exEq :: Int -> Int -> Int -> (Bool, Bool)
exEq a b c = (P (a, b) == P (b, c), P (a, b) /= P (b, c))

step :: Int -> Either Int Int
step n = if n > 5 then Left n else Right (n + 1)

exTrav :: [Int] -> (Either Int [Int], Either Int ())
exTrav xs = (traverse step xs, traverse_ step xs)
