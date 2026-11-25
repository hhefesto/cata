{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
-- a step in Reader over Except over State whose traversals run it on code
-- (transM at two steps of one knot, each with its own group)
module KnotRun where

import Control.Monad (when, (<=<))
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, asks, local, runReaderT)
import qualified Control.Monad.State.Strict as State
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata, project)
import Data.Map (Map)
import qualified Data.Map as Map

data TF r = Z | P r r | D Int r | L r | S r | V | E Int r r | A Int r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Fix TF

transM :: (Monad m) => (TF T -> m T) -> T -> m T
transM f = c where
  c = f <=< (c' . project)
  c' = \case
    s@(D _ _) -> pure s
    x         -> mapM c x

basicM :: Monad m => (TF T -> m T) -> TF T -> m T
basicM other x = f x where
  f = \case
    L (Fix (P a _)) -> pure a
    y@Z             -> pure (Fix y)
    y@(P _ _)       -> pure (Fix y)
    _               -> other x

stuckM :: Monad m => (TF T -> m T) -> TF T -> m T
stuckM other x = f x where
  f = \case
    S (Fix (P (Fix (D _ d)) e)) -> transM run d where
      run = basicM (stuckM other) . repl
      e' = project e
      repl = \case
        V  -> e'
        x' -> x'
    y@(D _ _) -> pure (Fix y)
    _         -> other x

exactM :: MonadReader Int m => (TF T -> m T) -> (TF T -> m T) -> TF T -> m T
exactM step other x = f x where
  pb bf = step . bf
  branch n a b = do
    known <- asks (\p -> if p > n then Just True else if p == n then Just False else Nothing)
    case known of
      Just True  -> a
      Just False -> b
      Nothing    -> (\u v -> Fix (E n u v)) <$> local (+ 1) a <*> b
  f = \case
    L (Fix (E n a b)) -> branch n (pb L a) (pb L b)
    y@(E _ _ _)       -> pure (Fix y)
    _                 -> other x

type M = ReaderT Int (ExceptT () (State.State (Int, Map Int [Int])))

analyze :: Int -> T -> T -> Maybe (Map Int [Int], T)
analyze budget input prog =
  case State.runState (runExceptT (runReaderT run 1)) (0, Map.empty) of
    (Left (), _)            -> Nothing
    (Right result, (_, fs)) -> Just (reverse <$> fs, result)
  where
  run = transM evalStep . cap input $ toT prog
  cap i p = Fix (S (Fix (P p i)))
  toT = cata (\case
    A 9 _ -> error "analyze: unexpected node"
    x     -> Fix x)
  evalStep :: TF T -> M T
  evalStep = basicM (stuckM (record (exactM evalStep unknown)))
  record other x = do
    (n, fs) <- State.get
    when (n >= budget) $ throwError ()
    path <- asks id
    let fs' = case x of
          A o _ -> Map.insertWith (<>) o [path] fs
          _     -> fs
    State.put (n + 1, fs')
    case x of
      A _ _ -> pure fired
      _     -> other x
  unknown _ = pure (Fix (D 0 (Fix Z)))
  fired = Fix (A 0 (Fix Z))

exAnalyze :: Int -> Maybe (Map Int [Int], T)
exAnalyze n = analyze n (Fix (P (Fix Z) (Fix (E 2 (Fix (P (Fix Z) (Fix Z))) (Fix Z)))))
  (Fix (D 1 (Fix (P (Fix (L (Fix V))) (Fix (P (Fix (A 4 (Fix Z))) (Fix (L (Fix (L (Fix (E 1 (Fix (P (Fix V) (Fix Z))) (Fix (P (Fix Z) (Fix Z)))))))))))))))
