module MuFn where

import qualified Control.Monad.State as State
import Control.Monad.State (State)
import qualified Data.Map as Map
import Data.Map (Map)

-- A mutual group whose member is handed a function in a Maybe (telomare's
-- specTerm: the applied closure and how to rebuild it)
data T = N Int | P T T | C Int T deriving (Show, Eq)

data St = St { bodies :: Map Int T, seen :: Int }

applied :: T -> Maybe (T, Int, T -> Int -> T)
applied (P x (C k y)) = Just (x, k, \x' k' -> P x' (C k' y))
applied _ = Nothing

spec :: T -> State St T
spec t
  | Just (x, k, rebuild) <- applied t = do
      x' <- spec x
      k' <- body k x'
      pure (rebuild x' k')
  | P a b <- t = P <$> spec a <*> spec b
  | otherwise = pure t

body :: Int -> T -> State St Int
body k x = do
  bs <- State.gets bodies
  case Map.lookup k bs of
    Nothing -> pure k
    Just b  -> do
      n <- State.gets seen
      if n > 5
        then pure k
        else do
          State.modify (\st -> st { seen = n + 1 })
          b' <- spec (P x b)
          State.modify (\st -> st { bodies = Map.insert (k + 10) b' (bodies st) })
          pure (k + 10)

run :: [(Int, T)] -> T -> (T, Int)
run bs t = let (r, st) = State.runState (spec t) (St (Map.fromList bs) 0) in (r, seen st)
