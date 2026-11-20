{-# LANGUAGE LambdaCase #-}
module LamCase where

-- cata's \case in an expression: an algebra of cata (telomare's
-- b2v = cata $ \case ...), a \case passed to map (one with guards), and
-- one applied at once

import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data ExprF r = Lit Int | Add r r | Neg r
  deriving (Eq, Show)

instance Functor ExprF where
  fmap _ (Lit n) = Lit n
  fmap f (Add a b) = Add (f a) (f b)
  fmap f (Neg a) = Neg (f a)

type Expr = Fix ExprF

build :: [Int] -> Expr
build [] = Fix (Lit 0)
build (x : xs)
  | x < 0 = Fix (Neg (build xs))
  | otherwise = Fix (Add (Fix (Lit x)) (build xs))

eval :: Expr -> Int
eval = cata $ \case
  Lit n -> n
  Add a b -> a + b
  Neg a -> negate a

evalList :: [Int] -> Int
evalList xs = eval (build xs)

depth :: Expr -> Int
depth = cata (\case
  Lit _ -> 0
  Add a b -> 1 + max a b
  Neg a -> 1 + a)

depthList :: [Int] -> Int
depthList xs = depth (build xs)

signs :: [Int] -> [Bool]
signs = map (\case
  0 -> False
  n -> n > 0)

firstOr :: Int -> [Int] -> Int
firstOr d xs = (\case
  [] -> d
  y : _ -> y) xs

classify :: [Maybe Int] -> [Int]
classify = map (\case
  Nothing -> 0
  Just n | n > 10 -> 2
         | otherwise -> 1)
