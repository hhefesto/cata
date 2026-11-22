{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
-- | Mutually recursive local functions (a where-bound group of two or
-- more), the shape of telomare's EAL.selfReferential (classIfaces and tau
-- call each other, both read the enclosing def's r0): pure, nonstructural
-- (an Int counting down), over a list sharing a free local, and in State.
module LocalMut where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State (State, gets, evalState)

isEvenL :: Int -> Bool
isEvenL n0 = ev n0 where
  ev n = if n <= (0 :: Int) then True else od (n - 1)
  od n = if n <= (0 :: Int) then False else ev (n - 1)

-- every other element equal to k, from the first
countAlt :: Int -> [Int] -> Int
countAlt k xs0 = goA xs0 where
  goA [] = 0
  goA (x : xs) = (if x == k then 1 else 0) + goB xs
  goB [] = 0
  goB (_ : xs) = goA xs

data Ty = TV Int | TPair Ty Ty | TCode Int

-- does a walk from r0 through the graph come back to r0: the path's
-- classes, as selfReferential's cycle
cyclic :: Map.Map Int [Ty] -> Int -> Maybe [Int]
cyclic g r0 = classes Set.empty r0 where
  classes vis r = walkL (Set.insert r vis) (Map.findWithDefault [] r g) r
  walkL vis ts r = case ts of
    [] -> Nothing
    t : rest -> case tau vis t of
      Just p -> Just (r : p)
      Nothing -> walkL vis rest r
  tau vis t = case t of
    TV _ -> Nothing
    TPair a b -> maybe (tau vis b) Just (tau vis a)
    TCode c -> if c == r0 then Just [] else if Set.member c vis then Nothing else classes vis c

-- the same in State over the graph, selfReferential's own shape: the
-- members walk a list through a monadic firstJustM given a member
cyclicS :: Int -> State (Map.Map Int [Ty]) (Maybe [Int])
cyclicS r0 = classes Set.empty r0 where
  classes vis r = do
    ts <- edgesOf r
    fmap (fmap (r :)) (firstJustM (tau (Set.insert r vis)) ts)
  tau vis = \case
    TV _ -> pure Nothing
    TPair a b -> tau vis a >>= maybe (tau vis b) (pure . Just)
    TCode c -> if c == r0 then pure (Just []) else if Set.member c vis then pure Nothing else classes vis c

-- monomorphic, as EAL's capturesOf: the group is not generalised
edgesOf :: Int -> State (Map.Map Int [Ty]) [Ty]
edgesOf r = gets (Map.findWithDefault [] r)

firstJustM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
firstJustM f xs = case xs of
  [] -> pure Nothing
  x : rest -> f x >>= \case
    Just y -> pure (Just y)
    Nothing -> firstJustM f rest

graph1 :: Map.Map Int [Ty]
graph1 = Map.fromList [(1, [TV 0, TPair (TV 1) (TCode 2)]), (2, [TCode 3]), (3, [TCode 1])]

ex1 :: Bool
ex1 = isEvenL 10 && not (isEvenL 7)

ex2 :: Int
ex2 = countAlt 3 [3, 3, 1, 3, 3, 2]

ex3 :: Maybe [Int]
ex3 = cyclic graph1 1

ex4 :: Maybe [Int]
ex4 = cyclic graph1 3

ex5 :: Maybe [Int]
ex5 = evalState (cyclicS 1) graph1
