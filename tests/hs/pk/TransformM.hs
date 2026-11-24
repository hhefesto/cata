-- Machine's transformNoDeferM: the walk in a monad of the package's own
{-# LANGUAGE LambdaCase, DeriveTraversable #-}
module TransformM where

import Control.Applicative (Applicative (..))
import Control.Monad ((<=<))
import Data.Fix (Fix (..))

data Acc a x = Acc { getAcc :: !a, getX :: x }
  deriving (Functor)

instance Monoid a => Applicative (Acc a) where
  pure = Acc mempty
  Acc u f <*> Acc v x = Acc (u <> v) (f x)
  liftA2 f (Acc u x) (Acc v y) = Acc (u <> v) (f x y)

instance Monoid a => Monad (Acc a) where
  Acc u x >>= f = case f x of Acc v y -> Acc (u <> v) y

data F r = Zero | Pair r r | Env | Defer Int r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type E = Fix F

transformM :: Monad m => (F E -> m E) -> E -> m E
transformM f = c where
  c = f <=< (c' . unFix)
  c' = \case
    s@(Defer _ _) -> pure s
    x             -> mapM c x

step :: F E -> Acc [Int] E
step = \case
  Env -> Acc [1] (Fix Zero)
  Pair a b -> Acc [2] (Fix (Pair b a))
  x -> pure (Fix x)

size :: E -> Int
size (Fix x) = case x of
  Zero -> 1
  Pair a b -> 2 * size a + size b
  Env -> 5
  Defer n a -> n + size a

exM :: Int -> ([Int], Int)
exM n = case transformM step (Fix (Pair (Fix Env) (Fix (Pair (Fix (Defer n (Fix Env))) (Fix Zero))))) of
  Acc xs e -> (xs, size e)

-- at a function over run-time values that calls the walk again
replace :: Int -> E -> Acc [Int] E
replace n = transformM go where
  go = \case
    Env -> if n > 2 then pure (Fix (Defer n (Fix Zero))) else replace (n + 1) (Fix (Pair (Fix Env) (Fix Zero)))
    x   -> step x

exReplace :: Int -> ([Int], Int)
exReplace n = case replace n (Fix (Pair (Fix Env) (Fix Env))) of Acc xs e -> (xs, size e)
