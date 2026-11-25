module ForDbg where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans (lift)
import Data.Bifunctor (second)
import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type M = StateT [String] (Either String)

data Ctx = Ctx { frames :: [Map String Int], here :: String }

warn :: Ctx -> String -> M ()
warn ctx w = modify' ((here ctx ++ w) :)

k1 :: [String] -> String -> M ()
k1 order c = do
  let ctx = Ctx { frames = [], here = c }
  forM_ order $ \k -> warn ctx k

k2 :: [String] -> String -> M Int
k2 order c = do
  let firsts = nubOn (\m -> length m) order
      ctx = Ctx { frames = [], here = c }
  forM_ order $ \k -> warn ctx (k ++ show (length firsts))
  pure (length firsts)
  where
    nubOn f = go Set.empty where
      go _ [] = []
      go seen (x : xs)
        | f x `Set.member` seen = go seen xs
        | otherwise = x : go (Set.insert (f x) seen) xs

k3 :: [(String, Int)] -> String -> M ()
k3 order c = do
  let own = second negate <$> order
      ctx = Ctx { frames = [], here = c }
  forM_ own $ \(k, v) -> warn ctx (k ++ show v)

k4 :: [String] -> Map String [String] -> String -> M [Ctx]
k4 order infos c = forM order $ \n -> moduleCtx n
  where
    moduleCtx name = do
      let ctx = Ctx { frames = [], here = c }
      forM_ order $ \k -> warn ctx k
      pure ctx

k5 :: [String] -> Map String [String] -> String -> M [Int]
k5 order infos c = forM order $ \n -> moduleCtx n
  where
    moduleCtx name = do
      let info = infos Map.! name
      forM_ info $ \k -> warn (Ctx [] k) k
      pure (length info)

k6 :: [String] -> Map String [String] -> String -> M [Int]
k6 order infos c = forM order $ \n -> moduleCtx n
  where
    moduleCtx name = do
      let info = Map.lookup name infos
      forM_ order $ \k -> warn (Ctx [] k) k
      pure (length info)

k7 :: [String] -> Map String [String] -> String -> M [Int]
k7 order infos c = forM order $ \n -> moduleCtx n
  where
    moduleCtx name = do
      forM_ order $ \k -> warn (Ctx [] k) (k ++ c)
      pure (length name)
