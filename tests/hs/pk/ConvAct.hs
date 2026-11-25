-- a function parameter whose answer is an action, at a partial one
-- (Driver's convertAbort, convertBasic)
{-# LANGUAGE DeriveFunctor, FlexibleContexts, LambdaCase #-}
module ConvAct where

import Control.Monad.State (State, modify, runState)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data F r = Z | P r r | Ab Int | Un Int r
  deriving (Eq, Show, Functor)

data T = TZ | TP T T | TA Int
  deriving (Eq, Show)

convBasic :: Monad m => (F (m T) -> m T) -> F (m T) -> m T
convBasic other = \case
  Z -> pure TZ
  P a b -> TP <$> a <*> b
  x -> other x

convAbort :: Monad m => (F (m T) -> m T) -> F (m T) -> m T
convAbort other = \case
  Ab n -> pure (TA n)
  x -> other x

conv :: Fix F -> State Int T
conv = cata (convBasic (convAbort rest)) where
  rest = \case
    Un n y -> do
      modify (+ n)
      y
    _ -> error "conv: unhandled"

exConv :: Int -> (T, Int)
exConv n = runState (conv (Fix (P (Fix (Un n (Fix (Ab n)))) (Fix Z)))) 0

-- total: an algebra of its own
conv2 :: Fix F -> State Int T
conv2 = cata (convBasic (convAbort (const (pure TZ))))

exConv2 :: Int -> (T, Int)
exConv2 n = runState (conv2 (Fix (P (Fix (Un n (Fix (Ab n)))) (Fix Z)))) 0
