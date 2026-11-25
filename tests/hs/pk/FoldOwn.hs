{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module FoldOwn where

-- Foldable's concat at a package's own functor (telomare's checkPattern)
data PF g r = Pair r r | Anno r g | Var String
  deriving (Functor, Foldable)

leaves :: PF Int [Int] -> [Int]
leaves p = case p of
  Anno inner g -> inner ++ [g]
  other        -> concat other
