-- == at Fix f, f's Eq1 derived via Generically1 (Resolve's Term3LiftingF)
{-# LANGUAGE DeriveGeneric, DeriveTraversable, DerivingVia, DerivingStrategies #-}
module FixEqG where

import Data.Fix (Fix (..))
import Data.Orphans ()
import Data.Functor.Classes (Eq1 (..))
import GHC.Generics (Generic1, Generically1 (..))

data G r = Nil | Cell Int r
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 G)

data F l r = Zero | Pair r r | Tag l (G r) | Name String r
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (F l))

type E = Fix (F Int)

newtype M = M [(Int, E)]

agree :: M -> M -> Bool
agree (M xs) (M ys) = and (zipWith (\(i, a) (j, b) -> i == j && not (a /= b)) xs ys)

build :: Int -> String -> E
build n s = Fix (Pair (Fix (Tag n (Cell n (Fix Zero)))) (Fix (Name s (Fix (Tag 1 Nil)))))

exAgree :: Int -> Int -> String -> String -> Bool
exAgree n m s t = agree (M [(0, build n s), (n, build m t)]) (M [(0, build m t), (n, build m s)])
