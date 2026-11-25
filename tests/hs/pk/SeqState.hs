{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
-- a conversion in State, its layers' actions partial (telomare's convertPT):
-- sequence of a layer, and an error at a function's type for what is left
module SeqState where

import qualified Control.Monad.State as State
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data BF r = Z | P r r deriving (Eq, Show, Functor, Foldable, Traversable)

data AF r = A Int r deriving (Eq, Show, Functor, Foldable, Traversable)

data TF r = TB (BF r) | TA (AF r) | TD Int r | TU Int | TC Int r r | TX r
  deriving (Functor, Foldable, Traversable)

data CF r = CB (BF r) | CA (AF r) | CD Int r
  deriving (Functor, Foldable, Traversable)

type T = Fix TF

type C = Fix CF

type B = State.State (Int, Int)

class Tree f where
  getB :: f r -> Maybe (BF r)
  getA :: f r -> Maybe (AF r)
  mkB :: BF r -> f r
  mkA :: AF r -> f r

instance Tree TF where
  getB = \case
    TB b -> Just b
    _    -> Nothing
  getA = \case
    TA b -> Just b
    _    -> Nothing
  mkB = TB
  mkA = TA

instance Tree CF where
  getB = \case
    CB b -> Just b
    _    -> Nothing
  getA = \case
    CA b -> Just b
    _    -> Nothing
  mkB = CB
  mkA = CA

pattern BFW :: Tree f => BF r -> f r
pattern BFW x <- (getB -> Just x) where
  BFW x = mkB x

pattern AFW :: Tree f => AF r -> f r
pattern AFW x <- (getA -> Just x) where
  AFW x = mkA x

convB :: (Tree f, Tree g, Monad m) => (f (m (Fix g)) -> m (Fix g)) -> f (m (Fix g)) -> m (Fix g)
convB other = \case
  BFW b -> Fix . BFW <$> sequence b
  x     -> other x

convA :: (Tree f, Tree g, Monad m) => (f (m (Fix g)) -> m (Fix g)) -> f (m (Fix g)) -> m (Fix g)
convA other = \case
  AFW b -> Fix . AFW <$> sequence b
  x     -> other x

deferS :: C -> B C
deferS x = do
  (n, u) <- State.get
  State.put (n + 1, u)
  pure . Fix $ CD n x

convert :: (Int -> Int) -> T -> C
convert ll = flip State.evalState (0, 0) . cata (f (convB (convA failConvert))) where
  failConvert = error "convert failed"
  f :: (TF (B C) -> B C) -> TF (B C) -> B C
  f other = \case
    TD _ x      -> x >>= deferS
    TU u        -> pure $ iterate (Fix . CB . P (Fix (CB Z))) (Fix (CB Z)) !! ll u
    TC o tc c   -> (\a b -> Fix (CA (A o (Fix (CB (P a b)))))) <$> tc <*> c
    x           -> other x

exConvert :: Int -> Bool -> C
exConvert n b = convert (+ 1) (Fix (TB (P (Fix (TD 9 (Fix (TA (A n (Fix (TU n))))))) (Fix (TC 2 (Fix (TD 1 (Fix (TB Z)))) (if b then Fix (TX (Fix (TB Z))) else Fix (TU 1)))))))
