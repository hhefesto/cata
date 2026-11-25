-- a def polymorphic in a functor (Desugar's rewriteOuterTag)
{-# LANGUAGE DeriveFunctor #-}
module HkPar where

import Control.Comonad.Cofree (Cofree (..))

data E r = V String | A r r
  deriving (Eq, Show, Functor)

retag :: anno -> Cofree a anno -> Cofree a anno
retag anno (_ :< x) = anno :< x

tags :: Cofree E Int -> [Int]
tags (n :< e) = case e of
  V _ -> [n]
  A a b -> n : tags a ++ tags b

term :: Int -> Cofree E Int
term n = n :< A (1 :< V "x") (retag (n + 2) (3 :< A (4 :< V "y") (5 :< V "z")))

exTags :: Int -> [Int]
exTags n = tags (retag (n + 10) (term n))

range :: Integer -> Integer -> [Integer]
range a b = [a .. b] ++ [x * 2 | x <- [1, 3 .. b]]
