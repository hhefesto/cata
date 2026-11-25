{-# LANGUAGE FlexibleContexts #-}
module RdExS where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, ask, asks, local, runReaderT)
import qualified Control.Monad.State as State

data T = L Int | N T T deriving (Eq, Show)

data Tr a = TL Int | TN a a deriving (Eq, Show)

instance Functor Tr where
  fmap _ (TL i)   = TL i
  fmap f (TN a b) = TN (f a) (f b)

instance Foldable Tr where
  foldr _ z (TL _)   = z
  foldr f z (TN a b) = f a (f b z)

instance Traversable Tr where
  traverse _ (TL i)   = pure (TL i)
  traverse f (TN a b) = TN <$> f a <*> f b

type M = ReaderT Int (ExceptT () (State.State (Int, [Int])))

count :: Int -> T -> M Int
count b t = do
  (n, xs) <- State.get
  when (n >= b) $ throwError ()
  d <- ask
  let n' = n + 1
  State.put (n', d : xs)
  case t of
    L i   -> pure (i + d)
    N l r -> (+) <$> local (+ 1) (count b l) <*> local (* 2) (count b r)

run :: Int -> Int -> T -> Either () (Int, (Int, [Int]))
run b d t = case State.runState (runExceptT (runReaderT (count b t) d)) (0, []) of
  (Left (), _) -> Left ()
  (Right v, s) -> Right (v, s)

-- a step at any reader, run at the stack
step :: MonadReader Int m => (a -> m b) -> Tr a -> m (Tr b)
step f x = do
  d <- asks (+ 1)
  case x of
    TL i   -> pure (TL (i + d))
    TN a b -> TN <$> local (const d) (f a) <*> local (* d) (f b)

leaf :: Int -> M Int
leaf x = do
  d <- ask
  if d > 50 then throwError () else State.modify (\(n, xs) -> (n + x, x : xs)) >> pure (x * d)

runStep :: Int -> Tr Int -> Either () (Tr Int, (Int, [Int]))
runStep d x = case State.runState (runExceptT (runReaderT (step leaf x) d)) (0, []) of
  (Left (), _) -> Left ()
  (Right v, s) -> Right (v, s)

runTrav :: Int -> Tr Int -> Either () (Tr Int)
runTrav d x = State.evalState (runExceptT (runReaderT (traverse leaf x) d)) (0, [])
