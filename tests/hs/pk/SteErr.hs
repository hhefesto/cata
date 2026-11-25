module SteErr where

import Control.Monad (forM, unless, when)
import Control.Monad.State.Strict (StateT, gets, modify', runStateT)
import Control.Monad.Trans (lift)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- StateT over Either with errors GHC throws (telomare's Bind)
data St = St { next :: Int, defs :: Map Int String, done :: Map Int Int }

type M = StateT St (Either String)

failWith :: String -> M a
failWith = lift . Left

getDef :: Int -> M String
getDef i = gets (Map.lookup i . defs) >>= \m -> case m of
  Just d  -> pure d
  Nothing -> error "unregistered"

size :: Int -> M Int
size i = gets (Map.lookup i . done) >>= \m -> case m of
  Just n  -> pure n
  Nothing -> do
    d <- getDef i
    when (d == "") $ failWith "empty"
    let n = length d
    unless (n < 1) $ modify' (\st -> st { done = Map.insert i n (done st) })
    pure n

sizeOf :: Int -> M Int
sizeOf i = size i >> gets (maybe (error "not done") id . Map.lookup i . done)

total :: [Int] -> M Int
total is = do
  ns <- forM is $ \i -> do
    n <- sizeOf i
    pure (n + i)
  pure (sum ns)

run :: [(Int, String)] -> [Int] -> Either String Int
run ds is = do
  (n, st) <- runStateT (total is) (St 0 (Map.fromList ds) Map.empty)
  pure (n + Map.size (done st))
