-- derived == at a type with a Fix among its fields
module EqFix where

import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..))

data E a = Z | P a a | A Int a deriving (Eq, Show)

instance Functor E where
  fmap _ Z       = Z
  fmap f (P a b) = P (f a) (f b)
  fmap f (A i a) = A i (f a)

instance Eq1 E where
  liftEq _ Z Z             = True
  liftEq t (P a b) (P c d) = t a c && t b d
  liftEq t (A i a) (A j b) = i == j && t a b
  liftEq _ _ _             = False

type X = Fix E

data Tree = Passes | Fails X | Undecided | Split Int Tree Tree deriving Eq

split :: Int -> Tree -> Tree -> Tree
split n a b
  | a == b    = a
  | otherwise = Split n a b

code :: Tree -> Int
code Passes        = 0
code (Fails _)     = 1
code Undecided     = 2
code (Split n a b) = 10 + n + code a + code b

build :: Int -> Tree
build n
  | n <= 0    = Passes
  | n == 1    = Fails (Fix (A 1 (Fix Z)))
  | n == 2    = Fails (Fix (P (Fix Z) (Fix (A 2 (Fix Z)))))
  | n == 3    = Undecided
  | otherwise = split n (Fails (Fix (A 1 (Fix Z)))) (Fails (Fix (A (n - 3) (Fix Z))))

exSplit :: Int -> Int -> Int
exSplit n m = code (split n (build n) (build m))

differ :: Int -> Int -> Bool
differ n m = build n /= build m
