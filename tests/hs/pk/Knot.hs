module Knot where

import Control.Applicative ((<|>))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- A Map that is its own, lazily (telomare's EAL: the bodies each body reaches),
-- and one asked for only where a case fails
type G = Map Int (String, [Int])

reaching :: G -> [(Int, [String])]
reaching g = [ (k, Set.toList (reachOf k)) | k <- Map.keys g ]
  where
    reach = Map.map (\(n, ks) -> Set.insert n (foldMap reachOf ks)) g
    reachOf k = Map.findWithDefault mempty k reach

costs :: Int -> G -> Int -> Either String [(Int, Either String Int)]
costs limit g k0 = case own k0 of
  Right n | n < limit -> Right [(k0, Right n)]
  Right n -> Right [(k0, Left (show n))]
  Left e -> case small e <|> twice e of
    Just n  -> Right [(n, Left e)]
    Nothing -> Right (Map.toList results)
  where
    own k = maybe (Left ("no " ++ show k)) (Right . length . fst) (Map.lookup k g)
    small e = if length e > limit then Just (length e) else Nothing
    twice e = if length e * 2 > limit then Just (100 `div` (length e - 5)) else Nothing
    results = Map.mapWithKey total g
    total _k (n, ks) = withDeps ks $ Right (length n)
    resultOf k = case Map.lookup k results of
      Just r  -> r
      Nothing -> Left ("missing " ++ show k)
    withDeps :: [Int] -> Either String a -> Either String a
    withDeps ks r = case [ k | k <- ks, Left _ <- [resultOf k] ] of
      k : _ -> Left ("dep " ++ show k)
      []    -> r

dag :: [(String, [Int])] -> G
dag ns = Map.fromList [ (i, (n, [ j | j <- ks, j > i || j < 0 ])) | (i, (n, ks)) <- zip [0 ..] ns ]

runReach :: [(String, [Int])] -> [(Int, [String])]
runReach = reaching . dag

runCosts :: Int -> [(String, [Int])] -> Int -> Either String [(Int, Either String Int)]
runCosts l ns = costs l (dag ns)
