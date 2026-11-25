module CataC where

import CataB
import qualified Control.Monad.State as State

c1 :: (Int -> Int) -> [Int] -> B O
c1 ren outer = foldr (pairS . pure . varP . ren) (pure ONil) outer

c2 :: (Int -> Int) -> [Int] -> B O
c2 ren outer = foldr (pairS . pure . var . ren) (pure ONil) outer

bad :: Int -> Int
bad n = if n > 2 then error "big" else n

r1 :: [Int] -> O
r1 xs = State.evalState (c1 bad xs) (0, 0)

r2 :: [Int] -> O
r2 xs = State.evalState (c2 bad xs) (0, 0)

r3 :: [Int] -> O
r3 xs = State.evalState (c1 (+ 1) xs) (0, 0)
