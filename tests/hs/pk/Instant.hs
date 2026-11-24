-- IC's instantiate: nested forM_ over run-time locals, a local action in
-- the inner one
{-# LANGUAGE LambdaCase, FlexibleContexts #-}
module Instant where

import Control.Monad (forM, forM_, when)
import Control.Monad.State (State, gets, modify, runState)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import qualified Data.IntMap.Strict as IntMap

data Port = Port Int Int
  deriving (Eq, Ord, Show)

data Kind = KDup Int | KPair
  deriving (Eq, Show)

data Node = Node { nodeKind :: Kind, nodePorts :: IntMap.IntMap Port }
  deriving (Eq, Show)

data Tpl = Tpl { tplExt :: Int, tplNodes :: IntMap.IntMap Node }
  deriving (Eq, Show)

data S = S { sNext :: Int, sTpls :: IntMap.IntMap Tpl, sWires :: [(Port, Port)], sKinds :: [Kind] }
  deriving (Eq, Show)

type M = ExceptT String (State S)

newNode :: Kind -> M Int
newNode k = do
  n <- gets sNext
  modify $ \st -> st { sNext = n + 1, sKinds = k : sKinds st }
  pure n

connect :: Port -> Port -> M ()
connect p q = modify $ \st -> st { sWires = (p, q) : sWires st }

instantiate :: Int -> Port -> Port -> M ()
instantiate tid envSrc resultDst = do
  tpl <- gets (IntMap.lookup tid . sTpls) >>= \case
    Just tpl -> pure tpl
    Nothing  -> throwError ("no template " <> show tid)
  base <- gets sNext
  copies <- fmap IntMap.fromList
    . forM [ (n, nd) | (n, nd) <- IntMap.toList (tplNodes tpl), n /= tplExt tpl ] $ \(n, nd) ->
      (,) n <$> newNode (relabel base (nodeKind nd))
  let translate (Port n s)
        | n == tplExt tpl = pure $ if s == 0 then envSrc else resultDst
        | otherwise = case IntMap.lookup n copies of
            Just m  -> pure (Port m s)
            Nothing -> throwError "instantiate: unmapped node"
  forM_ (IntMap.toList (tplNodes tpl)) $ \(n, nd) ->
    forM_ (IntMap.toList (nodePorts nd)) $ \(s, q) ->
      when (Port n s < q) $ do
        p' <- translate (Port n s)
        q' <- translate q
        connect p' q'
  where
    relabel base = \case
      KDup l -> KDup (base + l)
      k      -> k

exInst :: Int -> Int -> Either String ([(Port, Port)], [Kind])
exInst t a = case runState (runExceptT (instantiate t (Port 7 a) (Port 8 a))) st of
  (Left e, _) -> Left e
  (Right (), s) -> Right (sWires s, sKinds s)
  where
    st = S 10 (IntMap.fromList [(1, tpl)]) [] []
    tpl = Tpl 0 (IntMap.fromList [(0, Node KPair (IntMap.fromList [(0, Port 1 0), (1, Port 2 1)])), (1, Node (KDup a) (IntMap.fromList [(0, Port 0 0), (1, Port 2 0)])), (2, Node KPair (IntMap.fromList [(0, Port 1 1), (1, Port 0 1)]))])

-- an action bound by a let, run twice, in a local function too (EAL's
-- intrinsic: dataLeaf, childView)
leaf :: Int -> M [Int]
leaf a = do
  let fresh = (\n -> n * 10) <$> newNode (KDup a)
      pairUp k
        | k > 2 = do
            l <- fresh
            r <- fresh
            pure [l, r, k]
        | otherwise = (: []) <$> fresh
  xs <- pairUp a
  ys <- pairUp (a + 1)
  z <- fresh
  pure (xs <> ys <> [z])

exLeaf :: Int -> (Either String [Int], Int)
exLeaf a = case runState (runExceptT (leaf a)) (S 1 IntMap.empty [] []) of
  (r, s) -> (r, length (sKinds s))
