{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
-- a cata into a State, one case of whose algebra is partial
module PartSt where

import Control.Monad.State (State, evalState, get, put)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data TF r = U Int | D r | P r r | Z deriving (Eq, Show, Functor, Foldable, Traversable)

data EF r = S r | Env Int | Q r r | N deriving (Eq, Show, Functor, Foldable, Traversable)

mkQ :: Fix EF -> State Int (Fix EF)
mkQ x = do
  n <- get
  put (n + 1)
  pure (Fix (Q x (Fix (Env n))))

base :: (TF (State Int (Fix EF)) -> State Int (Fix EF)) -> TF (State Int (Fix EF)) -> State Int (Fix EF)
base other = \case
  Z     -> pure (Fix N)
  P a b -> (\x y -> Fix (Q x y)) <$> a <*> b
  x     -> other x

conv :: (Int -> Int) -> Fix TF -> Fix EF
conv ll = flip evalState 0 . cata (f (base failConv)) where
  failConv = error "conv failed"
  f :: (TF (State Int (Fix EF)) -> State Int (Fix EF)) -> TF (State Int (Fix EF)) -> State Int (Fix EF)
  f other = \case
    U i -> pure $ iterate (Fix . S) (Fix (Env 7)) !! ll i
    D x -> x >>= mkQ
    x   -> other x

exConv :: Int -> Fix EF
exConv n = conv (+ n) (Fix (P (Fix (D (Fix (U 2)))) (Fix (D (Fix (P (Fix Z) (Fix (U 1))))))))
