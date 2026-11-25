{-# LANGUAGE DeriveTraversable #-}
-- a functor with no field of its variable, whose derived fmap and traverse
-- GHC writes with coerce
module Phantom where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data I f = AnyF | IVar Int | Bnd [Int] Int deriving (Eq, Show, Functor, Foldable, Traversable)

data E r = Z | P r r | In (I r) deriving (Eq, Show, Functor, Foldable, Traversable)

reads' :: Fix E -> [Int]
reads' = cata (\x -> case x of { Z -> []; P a b -> a ++ b; In (IVar n) -> [n]; In (Bnd zs n) -> n : zs; In AnyF -> [] })

-- fmap at another type
tag :: Int -> E Int -> E (Int, Bool)
tag n = fmap (\x -> (x + n, x > n))

keep :: (a -> Maybe b) -> E a -> Maybe (E b)
keep = traverse

exKeep :: Int -> E Int -> Maybe (E Bool)
exKeep n = keep (\x -> if x > n then Nothing else Just (x == n))

iKeep :: I Int -> Maybe (I Bool)
iKeep = traverse (\x -> if x > 3 then Nothing else Just (x == 3))

iTag :: I Int -> I Bool
iTag = fmap (> 3)
