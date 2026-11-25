-- defs answering ExceptT e (State s) a (Control.Monad.State's Strict and
-- Lazy, mtl's classes, as telomare's IC and EAL have them), and defs whose
-- parameter passed unchanged to their own calls follows one that changes
-- (Fold puts such a template parameter first; the laws' inputs stay in h's
-- order)
module PkTyD where

import Control.Monad.Except
import Control.Monad.State.Strict (State)
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.State.Lazy as LState

data Err = Neg Int | Big
  deriving (Eq, Show)

type M = ExceptT Err (State Int)

tick :: Int -> M Int
tick k = do
  n <- State.get
  if k < 0 then throwError (Neg k) else State.put (n + k)
  pure (n * 2)

ticks :: [Int] -> M Int
ticks xs = case xs of
  [] -> State.get
  x : t -> tick x >> ticks t

bounded :: Int -> M Bool
bounded lim = do
  n <- State.get
  if n > lim then throwError Big else pure (n == lim)

push :: String -> ExceptT String (LState.State [String]) Int
push s = do
  xs <- LState.get
  if null s then throwError "empty" else LState.put (s : xs)
  pure (length xs)

countIn :: [Int] -> Int -> Int
countIn xs k = case xs of
  [] -> 0
  x : t -> (if x == k then 1 else 0) + countIn t k

dropUntil :: [Int] -> Int -> [Int]
dropUntil xs k = case xs of
  [] -> []
  x : t -> if x == k then t else dropUntil t k

-- telomare's Machine.isUnbounded: its local f's n, in a section passed
-- to filter, a template, so Fold's isUnbounded takes n first
reachesBelow :: [Int] -> Int -> Bool
reachesBelow s n = f s where
  f s'
    | null s' = True
    | elem n s' = False
    | otherwise = f (map (\x -> x - 1) (filter (>= n) s'))

-- partial, under ExceptT over State
orDie :: Int -> M Int
orDie n = if n > 1 then error "too big" else do
  s <- tick n
  pure (s + n)
