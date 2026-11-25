module LetMu where

import Control.Monad.Except
import Control.Monad.State.Strict (State)
import qualified Control.Monad.State.Strict as State

-- A let whose pattern names the whole and a part, under a recursion that
-- answers an action (telomare's EAL.envComponent)
data Sg = Sg Int Ty deriving (Eq, Show)
data Ty = Un | Pr Sg Sg deriving (Eq, Show)
data St = SL | SR deriving (Eq, Show)

type M = ExceptT String (State Int)

fresh :: M Sg
fresh = do
  n <- State.get
  State.put (n + 1)
  pure (Sg n Un)

check :: Ty -> Ty -> M ()
check (Pr (Sg a _) _) _ | a > 5 = throwError "deep"
check _ _ = pure ()

component :: Sg -> [St] -> M ([Int], Sg)
component s0 = go s0 [] where
  go sig acc [] = pure (reverse acc, sig)
  go (Sg _ t) acc (s : rest) = do
    sl <- fresh
    sr <- fresh
    check t (Pr sl sr)
    let next@(Sg b _) = case s of
          SL -> sl
          SR -> sr
    go next (b : acc) rest

runC :: Int -> [St] -> (Either String ([Int], Sg), Int)
runC n ss = State.runState (runExceptT (component (Sg 0 Un) ss)) n
