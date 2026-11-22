module Seq where

-- Traversable's sequence (and sequenceA) at a list, at the monads telomare
-- runs it in: ExceptT e (State s) (EAL's presolve: `or <$> sequence [..]`),
-- State, Either and Maybe; and a template argument whose lambda binds by a
-- pattern the name of a parameter elsewhere (EAL's selfReferential:
-- `firstJustM (\(t, ty) -> .. ty) starts` beside `tau vis t`).

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, get, put, runState)

type M = ExceptT String (State Int)

-- counts each step, fails on a negative number
step :: Int -> M Bool
step x = do
  n <- get
  put (n + 1)
  if x < 0 then throwError "negative" else return (x > n)

anyStep :: Int -> Int -> Int -> Int -> (Either String Bool, Int)
anyStep a b c s = runState (runExceptT (or <$> sequence [step a, step b, step c])) s

-- State alone
tick :: Int -> State Int Int
tick k = do
  s <- get
  put (s + 1)
  return (s + k)

ticks :: Int -> Int -> Int -> ([Int], Int)
ticks a b s = runState (sequence [tick a, tick b, tick a]) s

ticksA :: Int -> Int -> ([Int], Int)
ticksA a s = runState (sequenceA [tick a, tick s]) s

allJust :: [Maybe Int] -> Maybe [Int]
allJust xs = sequence xs

allRight :: [Either String Int] -> Either String [Int]
allRight xs = sequence xs

-- the first Just f gives, in order
firstJust :: (a -> Maybe b) -> [a] -> Maybe b
firstJust _ [] = Nothing
firstJust f (x : xs) = maybe (firstJust f xs) Just (f x)

-- t is bound by the lambda's pattern, and is grow's parameter too
grow :: Int -> [(Int, Int)] -> Maybe Int
grow t ps = firstJust (\(t, u) -> if u > 2 then Just (t + u) else Nothing) ps
