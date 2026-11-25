module SeqSt where

import Control.Monad (unless)
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import qualified Data.Map as Map

-- seq before an action (telomare's cycleStep)
step :: Map.Map Int Int -> [Int] -> State [Int] Int
step m xs = do
  let touched = Map.map (+ 1) m
  unless (null xs) $ touched `seq` pure ()
  State.modify (Map.elems touched ++)
  pure (Map.size touched)

run :: [(Int, Int)] -> [Int] -> (Int, [Int])
run m xs = State.runState (step (Map.fromList m) xs) []

force :: Int -> Int -> Int
force a b = (100 `div` a) `seq` b
