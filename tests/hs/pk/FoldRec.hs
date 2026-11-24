-- a recursion through a derived foldMap and the list's inside it (Fast's
-- positionsIn)
{-# LANGUAGE DeriveTraversable #-}
module FoldRec where

import Control.Comonad.Cofree (Cofree (..))

data F r = Var String | App r r | Let [(String, r)] r | Many [r]
  deriving (Functor, Foldable, Traversable)

type T = Cofree F Int

positions :: T -> [Int]
positions (loc :< term) = maybe id (:) (key loc) (foldMap positions term)

key :: Int -> Maybe Int
key n = if n > 2 then Just n else Nothing

exPositions :: Int -> Int -> [Int]
exPositions a b = positions (a :< Let [("x", b :< Var "y"), ("z", 5 :< App (a :< Var "q") (9 :< Var "r"))] (b :< Many [7 :< Var "s", a :< Var "t"]))
