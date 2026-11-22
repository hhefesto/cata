{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module LocalRec where

-- EAL's findB in its shape: a where-bound recursive `go` with no
-- signature, which Haskell 2010 generalises over its monad (MonadState
-- UF m => Int -> m Int), used at one monad: union-find's find with path
-- compression, at State and at ExceptT over State.

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map

data UF = UF { ufParents :: Map.Map Int Int, ufSteps :: Int }

type UFM = State.State UF

type UFE = ExceptT String (State.State UF)

find :: Int -> UFM Int
find i = go i where
  go j = State.gets (Map.lookup j . ufParents) >>= \case
    Nothing -> pure j
    Just p -> do
      r <- go p
      unless (r == p) . State.modify $ \st ->
        st { ufParents = Map.insert j r (ufParents st) }
      pure r

findE :: Int -> UFE Int
findE i = go i where
  go j = State.gets (Map.lookup j . ufParents) >>= \case
    Nothing -> pure j
    Just p -> do
      State.modify $ \st -> st { ufSteps = ufSteps st + 1 }
      r <- go p
      unless (r == p) . State.modify $ \st ->
        st { ufParents = Map.insert j r (ufParents st) }
      pure r

-- a parent map whose parents are smaller, so every chain ends
start :: [(Int, Int)] -> UF
start ps = UF (Map.fromList [(j, p) | (j, p) <- ps, p < j]) 0

root :: [(Int, Int)] -> Int -> (Int, [(Int, Int)])
root ps i = fmap (Map.toList . ufParents) (State.runState (find i) (start ps))

-- a root at most k, and the steps taken: else the ExceptT's failure
rootUpTo :: Int -> [(Int, Int)] -> Int -> (Either String Int, Int)
rootUpTo k ps i = fmap ufSteps (State.runState (runExceptT (check =<< findE i)) (start ps))
  where
    check r = if r > k then throwError "root too big" else pure r
