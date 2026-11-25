{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
-- a Reader over Except over State run on a partial function's answer: the
-- action is a local value made of it
module RunPart where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State.Strict (State, get, put, runState)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import Data.Map (Map)
import qualified Data.Map as Map

data TF r = Z | P r r | N Int | A r deriving (Eq, Show, Functor, Foldable, Traversable)

type M = ReaderT Int (ExceptT () (State (Int, Map Int [Int])))

toT :: Fix TF -> Fix TF
toT = cata (\case
  A _ -> error "toT: unexpected node"
  x   -> Fix x)

walk :: (TF (Fix TF) -> M (Fix TF)) -> Fix TF -> M (Fix TF)
walk f = go where
  go (Fix x) = case x of
    A _ -> pure (Fix x)
    _   -> traverse go x >>= f

cap :: Fix TF -> Fix TF
cap x = Fix (P (Fix Z) x)

analyze :: Int -> Int -> Fix TF -> Maybe (Map Int [Int], Fix TF)
analyze budget at prog =
  case runState (runExceptT (runReaderT run at)) (0, Map.empty) of
    (Left (), _)            -> Nothing
    (Right result, (_, fs)) -> Just (reverse <$> fs, result)
  where
  run = walk step . cap $ toT prog
  step :: TF (Fix TF) -> M (Fix TF)
  step = record (\x -> pure (Fix x))
  record other x = do
    (n, fs) <- get
    when (n >= budget) $ throwError ()
    path <- ask
    let fs' = case x of
          N m | m > path -> Map.insertWith (<>) m [path] fs
          _              -> fs
    put (n + 1, fs')
    case x of
      N 7 -> pure (Fix Z)
      _   -> other x

exAnalyze :: Int -> Maybe (Map Int [Int], Fix TF)
exAnalyze n = analyze n 2 (Fix (P (Fix (N 3)) (Fix (P (Fix (N 1)) (Fix (N 7))))))

-- a partial function a point-free local holds, given to a local function
size :: Int -> Fix TF -> Either Int Int
size n x = tidy (walkE (cap x)) where
  sizes = cata (\case
    Z     -> 0
    P a b -> a + b
    N i   -> i
    A _   -> error "size: A")
  walkE t = if n > 3 then Left n else Right t
  tidy r = case r of
    Left k  -> Left (k + 1)
    Right t -> case sizes t of
      0 -> Left 0
      k -> Right (k * n)
