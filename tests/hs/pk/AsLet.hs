module AsLet where

import Control.Monad.Except
import Control.Monad.State

data S = SL | SR deriving (Eq, Show)

data Sg = Sg Int Int deriving (Eq, Show)

type M = ExceptT String (State Int)

fresh :: M Sg
fresh = do
  n <- get
  put (n + 1)
  pure (Sg n n)

-- 0 is not covered
unify :: Int -> Int -> M ()
unify 1 _ = pure ()
unify 2 b = modify (+ b)

comp :: Int -> [S] -> M ([Int], Sg)
comp k = go (Sg k k) []
  where
    go sig acc [] = pure (reverse acc, sig)
    go (Sg _ t) acc (s : rest) = do
      sl <- fresh
      sr <- fresh
      unify t 3
      let next@(Sg b _) = case s of
            SL -> sl
            SR -> sr
      go next (b : acc) rest

run :: Int -> [S] -> (Either String ([Int], Sg), Int)
run k ss = runState (runExceptT (comp k ss)) 1
