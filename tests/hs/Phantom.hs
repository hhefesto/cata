{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Phantom where

-- Data.Foldable's default foldr ($dmfoldr), which GHC's derived Foldable
-- leaves in place at a type whose variable is phantom (telomare's
-- AbortableF, IndexedInputF): Base's model's foldrDefault.

import qualified Data.Foldable as F

data AbF f = AbortF | AbortedF Int
  deriving (Functor, Foldable)

data T a = L | N a (T a)
  deriving (Functor, Foldable)

sumAb :: AbF Int -> Int
sumAb = F.foldr (+) 0

ab :: Int -> AbF Int
ab n = if n > 0 then AbortedF n else AbortF

ex1 :: Int -> Int
ex1 n = sumAb (ab n) + F.foldr (+) 1 (ab (n - 2))

ex2 :: Int -> [Int]
ex2 n = F.foldr (:) [] (ab n) ++ F.foldr (:) [] (N n (N (n + 1) L))

ex3 :: Int -> String
ex3 n = F.fold (AbortedF n :: AbF String) ++ F.fold (N "a" (N (show n) L))
