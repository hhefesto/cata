-- free's unwrap at Cofree (Resolve's letsToApps, process2Term)
{-# LANGUAGE DeriveFunctor #-}
module Unwrap where

import Control.Comonad.Cofree (Cofree (..), unwrap)

data F r = Leaf Int | Node r r
  deriving (Functor)

type T = Cofree F Int

depth :: T -> Int
depth t = case unwrap t of
  Leaf n -> n
  Node a b -> 1 + max (depth a) (depth b)

exDepth :: Int -> Int
exDepth n = depth (n :< Node (1 :< Leaf n) (2 :< Node (3 :< Leaf (n + 1)) (4 :< Leaf 0)))
