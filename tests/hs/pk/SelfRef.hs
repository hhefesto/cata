-- EAL's selfReferential's shape: a where's mutually recursive locals, a
-- lambda \(t, Sigma _ ty) -> .. lifted where tau's parameter t is in scope
{-# LANGUAGE LambdaCase #-}
module SelfRef where

import Control.Monad (forM)
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Set as Set

data Sigma = Sigma Int T
  deriving (Eq, Show)
data T = VarT Int | DataT | PairT Sigma Sigma | CodeT Int
  deriving (Eq, Show)

type M = ExceptT String (State (Map.Map Int [(Int, Sigma)]))

look :: Int -> M [(Int, Sigma)]
look r = gets (Map.findWithDefault [] r)

walkT :: T -> M T
walkT t = pure t

firstJustM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
firstJustM _ []     = pure Nothing
firstJustM f (x:xs) = f x >>= maybe (firstJustM f xs) (pure . Just)

selfRef :: Int -> M (Maybe [Int])
selfRef r0 = classIfaces Set.empty r0 where
  classIfaces vis r = do
    infos <- look r
    let vis' = Set.insert r vis
    starts <- fmap concat . forM infos $ \(t, s) -> do
      a <- argumentOf s
      pure [(t, a), (t, s)]
    firstJustM (\(t, Sigma _ ty) -> fmap (t :) <$> tau vis' ty) starts
  argumentOf (Sigma b t) = walkT t >>= \case
    PairT arg _caps -> pure arg
    _notPair -> pure (Sigma b DataT)
  tau vis t = walkT t >>= \case
    VarT _ -> pure Nothing
    DataT -> pure Nothing
    PairT (Sigma _ x) (Sigma _ y) ->
      tau vis x >>= maybe (tau vis y) (pure . Just)
    CodeT c -> do
      if c == r0 then pure (Just [])
        else if Set.member c vis then pure Nothing
        else classIfaces vis c

runSelfRef :: Int -> [(Int, [(Int, Sigma)])] -> Either String (Maybe [Int])
runSelfRef r env = evalState (runExceptT (selfRef r)) (Map.fromList env)

exSelf :: Int -> Either String (Maybe [Int])
exSelf r = runSelfRef r [(1, [(7, Sigma 0 (CodeT 2))]), (2, [(8, Sigma 0 (PairT (Sigma 1 DataT) (Sigma 1 (CodeT 1))))])]
