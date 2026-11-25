module ForNest where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans (lift)
import Data.Bifunctor (second)
import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set

-- StateT over Either: nested forM_ over lists and a Maybe, their functions
-- partial (a Map's !), over a local function's values (telomare's Bind)
data Info = Info { keysOf :: Map String (Int, Bool), names :: [String] }

data Ctx = Ctx { frames :: [Map String (Int, Bool)], here :: String }

type M = StateT [String] (Either String)

warn :: Ctx -> String -> M ()
warn ctx w = modify' ((here ctx ++ w) :)

failWith :: String -> M a
failWith = lift . Left

scopes :: [(String, [String])] -> [(String, [(Maybe String, String)])] -> Either String ([Int], [String])
scopes modules imps = runStateT (program (map fst modules)) []
  where
    program order = do
      infos <- fmap Map.fromList . forM order $ \name -> do
        when (name == "") $ failWith "empty"
        pure (name, Info (Map.fromList (zipWith (\i k -> (k, (i, even i))) [0 ..] (maybe [] id (lookup name modules)))) [name])
      ctxs <- forM order $ \name -> moduleCtx infos name
      pure (length . frames <$> ctxs)
    importsOf name = maybe [] id (lookup name imps)
    moduleCtx infos name = do
      let info = infos Map.! name
          imports = [ (m, q, length m) | (q, m) <- importsOf name ]
          firsts = nubOn (\(m, q, _) -> (m, q)) imports
          layer (m, q, n) =
            ( n
            , Map.fromList [ (maybe k (\q' -> q' ++ "." ++ k) q, v) | (k, v) <- Map.toList (keysOf (infos Map.! m)) ] )
          layers = layer <$> firsts
          own = second not <$> keysOf info
          ctx = Ctx { frames = own : (snd <$> reverse layers), here = concat (mapMaybe (\(_, q, _) -> q) firsts) }
      forM_ (zip [0 :: Int ..] layers) $ \(n, (loc, keys)) ->
        forM_ (Map.keys keys) $ \k ->
          forM_ (find (Map.member k . snd) (reverse (take n layers))) $ \(_, earlier) ->
            warn ctx (show loc ++ k ++ show (fst (earlier Map.! k)))
      forM_ (Map.toList own) $ \(k, (loc, _)) ->
        forM_ (find (Map.member k . snd) (reverse layers)) $ \(_, keys) ->
          unless (take 1 k == "_") $ warn ctx (show loc ++ k ++ show (fst (keys Map.! k)))
      pure ctx
    nubOn f = go Set.empty where
      go _ [] = []
      go seen (x : xs)
        | f x `Set.member` seen = go seen xs
        | otherwise = x : go (Set.insert (f x) seen) xs

-- break at a function with a partial call in it
members :: Int -> [Int] -> [Int]
members i active =
  let ms = reverse (i : takeWhile (/= i) active)
      (before, from) = break (== minimum ms) ms
  in from ++ before
