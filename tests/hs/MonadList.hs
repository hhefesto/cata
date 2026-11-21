module MonadList where

-- Control.Monad's list functions at the monads telomare runs them in:
-- filterM and zipWithM_ at ExceptT e (State s) (EAL's equalityStep,
-- unifyTagInfo), traverse_ at Either (Expand's expandTerm), and mapM,
-- mapM_, foldM, filterM, zipWithM_ at Either, Maybe and State.

import Control.Monad (filterM, foldM, zipWithM_)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, get, modify, put, runState)
import Data.Foldable (for_, traverse_)

type M = ExceptT String (State Int)

-- counts each look, fails on a negative number
isBig :: Int -> M Bool
isBig x = do
  modify (+ 1)
  if x < 0 then throwError "negative" else return (x > 2)

bigs :: [Int] -> Int -> (Either String [Int], Int)
bigs xs s = runState (runExceptT (filterM isBig xs)) s

addPair :: Int -> Int -> M ()
addPair a b = do
  n <- get
  if a == b then throwError "same" else put (n + a * b)

pairUp :: [Int] -> [Int] -> Int -> (Either String (), Int)
pairUp xs ys s = runState (runExceptT (zipWithM_ addPair xs ys)) s

-- State alone
look :: Int -> State Int Bool
look x = do
  modify (+ x)
  return (even x)

evens :: [Int] -> Int -> ([Int], Int)
evens xs s = runState (filterM look xs) s

mulInto :: Int -> Int -> State Int ()
mulInto a b = modify (+ a * b)

dotS :: [Int] -> [Int] -> Int -> ((), Int)
dotS xs ys s = runState (zipWithM_ mulInto xs ys) s

-- Either
check :: Int -> Either String ()
check x = if x < 0 then Left ("negative: " ++ show x) else Right ()

checkAll :: [Int] -> Either String ()
checkAll xs = traverse_ check xs

checkFor :: [Int] -> Either String ()
checkFor xs = for_ xs check

halve :: Int -> Either String Int
halve x = if even x then Right (x `div` 2) else Left ("odd: " ++ show x)

halves :: [Int] -> Either String [Int]
halves xs = mapM halve xs

sumHalves :: [Int] -> Either String Int
sumHalves xs = foldM (\a x -> fmap (+ a) (halve x)) 0 xs

keepSmall :: [Int] -> Either String [Int]
keepSmall xs = filterM (\x -> if x > 100 then Left "huge" else Right (x < 10)) xs

sameLen :: [Int] -> [Int] -> Either String ()
sameLen xs ys = zipWithM_ (\a b -> if a == b then Right () else Left "differ") xs ys

-- Maybe
safeDiv :: Int -> Maybe Int
safeDiv x = if x == 0 then Nothing else Just (100 `div` x)

divs :: [Int] -> Maybe [Int]
divs xs = mapM safeDiv xs

divSum :: [Int] -> Maybe Int
divSum xs = foldM (\a x -> fmap (+ a) (safeDiv x)) 0 xs

nonZeroEvens :: [Int] -> Maybe [Int]
nonZeroEvens xs = filterM (\x -> if x == 0 then Nothing else Just (even x)) xs
