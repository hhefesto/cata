{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
-- a step that runs a whole traversal of itself (transM step), in an
-- applicative that sums: step and transM's copy at it are one knot
module StepKnot where

import Control.Monad ((<=<))
import Data.Fix (Fix (..))
import Data.Functor.Foldable (project)

data TF r = Z | P r r | D Int r | L r | W Int r | E r r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Fix TF

data Acc a = Acc Int a deriving (Eq, Show)

instance Functor Acc where
  fmap f (Acc n a) = Acc n (f a)

instance Applicative Acc where
  pure = Acc 0
  Acc n f <*> Acc m a = Acc (n + m) (f a)
  liftA2 f (Acc n a) (Acc m b) = Acc (n + m) (f a b)

instance Monad Acc where
  Acc n a >>= k = case k a of Acc m b -> Acc (n + m) b

transM :: (Traversable f, Monad m, f ~ TF) => (f T -> m T) -> T -> m T
transM f = c where
  c = f <=< (c' . project)
  c' = \case
    s@(D _ _) -> pure s
    x         -> mapM c x

basicM :: Monad m => (TF T -> m T) -> TF T -> m T
basicM other = \case
  L (Fix (P a _)) -> pure a
  x@Z             -> pure (Fix x)
  x@(P _ _)       -> pure (Fix x)
  x               -> other x

superM :: Monad m => (TF T -> m T) -> (TF T -> m T) -> TF T -> m T
superM step other x = f x where
  pb bf = step . bf
  f = \case
    L (Fix (E a b)) -> mk <$> pb L a <*> pb L b
    y@(E _ _)       -> pure (Fix y)
    _               -> other x
  mk a b = Fix (E a b)

size :: Int -> T -> Either Int (Int, T)
size fuel x = tidy . transM step $ mx where
  mx = Fix (P x (Fix Z))
  tidy (Acc n r) = if n > fuel then Left n else Right (n, r)
  checkS other = \case
    W o c -> do
      checked <- transM step (Fix (L c))
      pure $ case checked of
        Fix Z -> Fix (D o checked)
        _     -> checked
    y -> other y
  stuck err = \case
    y@(D _ _) -> Acc 1 (Fix y)
    y@(L _)   -> Acc 2 (Fix y)
    y         -> err y
  step = basicM (superM step (checkS (stuck unhandled)))
  unhandled y = error ("size: unexpected " ++ (case y of { P _ _ -> "P"; _ -> "other" }))

exSize :: Int -> Either Int (Int, T)
exSize n = size n (Fix (P (Fix (W 3 (Fix (P (Fix (L (Fix (P (Fix Z) (Fix Z))))) (Fix Z))))) (Fix (L (Fix (E (Fix (P (Fix Z) (Fix Z))) (Fix (D 1 (Fix Z)))))))))
