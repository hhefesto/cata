-- sequence of a list of actions written out, one of them partial (EAL's
-- presolve); a local function polymorphic over a Map's values (its blockOf)
module SeqLit where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

type M = ExceptT String (State [Int])

stepA, stepB :: Int -> M Bool
stepA n = do
  modify (n :)
  pure (n > 2)
stepB n = if n > 5 then throwError "big" else case n of
  4 -> error "four"
  _ -> do
    xs <- get
    pure (length xs > 1)

rounds :: Int -> M Int
rounds n = do
  changed <- or <$> sequence [stepA n, stepB n, stepA (n + 1)]
  if changed && n > 0 then rounds (n - 1) else pure n

exRounds :: Int -> (Either String Int, [Int])
exRounds n = runState (runExceptT (rounds n)) []

blocks :: Int -> [Int] -> ([(Int, Int)], [(Int, String)])
blocks v xs =
  let blockOf :: Map Int a -> [(Int, a)]
      blockOf = Map.toAscList . snd . Map.split (v - 1)
      m = Map.fromList (zip [0 ..] xs)
  in (blockOf m, blockOf (Map.map show m))
