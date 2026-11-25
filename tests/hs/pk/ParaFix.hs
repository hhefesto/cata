module ParaFix where

import Control.Applicative ((<|>))
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata, para)

data E a = Z | P a a | A Int a | D a deriving (Eq, Show)

instance Functor E where
  fmap _ Z       = Z
  fmap f (P a b) = P (f a) (f b)
  fmap f (A i a) = A i (f a)
  fmap f (D a)   = D (f a)

instance Foldable E where
  foldr _ z Z       = z
  foldr f z (P a b) = f a (f b z)
  foldr f z (A _ a) = f a z
  foldr f z (D a)   = f a z

size :: Fix E -> Int
size = cata (\x -> case x of { Z -> 1; P a b -> a + b + 1; A _ a -> a; D a -> a + 1 })

-- the first A outside every D, with the size under it
fired :: Fix E -> Maybe (Int, Int)
fired = para $ \x -> case x of
  D _         -> Nothing
  A o (m, im) -> im <|> Just (o, size m)
  y           -> foldr ((<|>) . snd) Nothing y

-- two actions in Maybe, the first one's answer
both :: Maybe Int -> Maybe Bool -> Maybe Int
both a b = a <* b

seqPair :: (Int, Either Bool Int) -> Either Bool (Int, Int)
seqPair = sequence
