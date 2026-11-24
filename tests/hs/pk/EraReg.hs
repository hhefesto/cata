-- IC's eraRegion: a where's action (dropLeaf, no parameters, a State
-- function) that the fuelled group's members take, with a where function
-- (dropPair) that calls the def back
module EraReg where

import Control.Monad.State

data Shape = SData | SPair Shape Shape
  deriving (Eq, Show)

type M = State [Int]

note :: String -> M ()
note s = modify (length s :)

peer :: Int -> M Int
peer n = gets (\xs -> n + length xs)

eraRegion :: Shape -> Int -> M ()
eraRegion shape p = gets length >>= \k -> case (shape, k > 3) of
  (SData, _) -> dropLeaf
  (SPair s1 s2, False) -> dropPair s1 s2
  _frontier -> note "frontier"
  where
    n = p * 2
    dropLeaf = do
      modify (n :)
      note "drop"
    dropPair s1 s2 = do
      a <- peer n
      b <- peer (n + 1)
      dropLeaf
      eraRegion s1 a
      eraRegion s2 b

runEra :: Shape -> Int -> [Int]
runEra s p = execState (eraRegion s p) []
