-- catas whose algebra is partial: an error at some layer, a converter given
-- an error as its other case (Driver's funWrapWith), at Cofree too
{-# LANGUAGE DeriveFunctor, LambdaCase #-}
module PartCata where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import Data.Functor.Identity (Identity (..))

data F r = Z | S r | P r r | M [r]
  deriving (Eq, Show, Functor)

data G r = GZ | GS r
  deriving (Eq, Show, Functor)

total :: Fix F -> Int
total = cata $ \case
  Z -> 0
  S n -> if n > 3 then error ("total: " ++ show n) else n + 1
  P a b -> a + b
  M xs -> sum xs

build :: Int -> Fix F
build n = if n <= 0 then Fix Z else if n > 4 then Fix (M [build (n - 3), Fix Z]) else Fix (S (Fix (P (build (n - 1)) (Fix Z))))

exTotal :: Int -> Int
exTotal n = total (build n)

convG :: Monad m => (F (m (Fix G)) -> m (Fix G)) -> F (m (Fix G)) -> m (Fix G)
convG other = \case
  Z -> pure (Fix GZ)
  S r -> Fix . GS <$> r
  x -> other x

toG :: Fix F -> Fix G
toG = runIdentity . cata (convG (\_ -> error "toG: no such layer"))

sizeG :: Fix G -> Int
sizeG = cata $ \case
  GZ -> 1
  GS n -> n + 1

chain :: Int -> Fix F
chain n = if n <= 0 then Fix Z else if n > 5 then Fix (P (Fix Z) (Fix Z)) else Fix (S (chain (n - 1)))

exToG :: Int -> Int
exToG n = sizeG (toG (chain n))

type T = Cofree F Int

depth :: T -> Int
depth = cata $ \case
  a C.:< Z -> a
  a C.:< S n -> if a == n then error "depth: same" else a + n
  a C.:< P x y -> max x y + a
  _ C.:< M xs -> length xs

exDepth :: Int -> Int -> Int
exDepth a b = depth (a :< S (b :< P (1 :< Z) (a :< S (2 :< Z))))
