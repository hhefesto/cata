module Exc where

-- cata's ExceptT rule: ExceptT e (State s) as S -> Either E A & S

import Control.Monad (foldM, forM, forM_, unless, void, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, evalState, execState, get, gets, modify, modify', put, runState)

type M = ExceptT String (State Int)

tick :: Int -> M Int
tick x = do
  n <- get
  put (n + x)
  return n

guardSmall :: Int -> M ()
guardSmall n = when (n > 1) (throwError "too big")

step :: Int -> M Int
step x = do
  guardSmall x
  modify (+ 1)
  tick x

steps :: [Int] -> Int -> (Either String [Int], Int)
steps xs s = runState (runExceptT (mapM step xs)) s

stepsFor :: [Int] -> Int -> (Either String [Int], Int)
stepsFor xs s = runState (runExceptT (forM xs step)) s

addTick :: Int -> Int -> M Int
addTick acc x = do
  _ <- tick 1
  return (acc + x)

sumUp :: [Int] -> Int -> (Either String Int, Int)
sumUp xs s = runState (runExceptT (foldM addTick 0 xs)) s

checkAll :: [Int] -> Int -> (Either String (), Int)
checkAll xs s = runState (runExceptT (forM_ xs guardSmall)) s

limited :: Int -> Int -> Either String Int
limited x s = evalState (runExceptT (step x)) s

counted :: Int -> Int -> Int
counted x s = execState (runExceptT (unless (x == 0) (void (tick x)))) s

doubled :: Int -> Int -> (Either String Int, Int)
doubled x s = runState (runExceptT (fmap (* 2) (step x))) s

peek :: Bool -> Int -> (Either String Int, Int)
peek b s = runState (runExceptT (if b then gets (* 3) else throwError "no")) s

bump :: Int -> (Either String (), Int)
bump s = runState (runExceptT (modify' (+ 2) *> modify (* 2))) s

-- State alone: mapM_, mapM, foldM
counter :: Int -> State Int Int
counter x = do
  n <- get
  put (n + x)
  return (n * x)

counters :: [Int] -> Int -> ([Int], Int)
counters xs s = runState (mapM counter xs) s

totalS :: [Int] -> Int -> Int
totalS xs s = execState (mapM_ counter xs) s

foldS :: [Int] -> Int -> (Int, Int)
foldS xs s = runState (foldM (\a x -> fmap (+ a) (counter x)) 0 xs) s

-- when, unless, void, =<< and *> at Maybe and Either
whenM :: Bool -> Maybe () -> Maybe ()
whenM b m = when b m

unlessE :: Bool -> Either Int () -> Either Int ()
unlessE b m = unless b m

voidE :: Either Int Int -> Either Int ()
voidE e = void e

half :: Int -> Maybe Int
half x = if even x then Just (x `div` 2) else Nothing

halfR :: Maybe Int -> Maybe Int
halfR m = half =<< m

thenE :: Either Int Int -> Either Int Int -> Either Int Int
thenE a b = a *> b
