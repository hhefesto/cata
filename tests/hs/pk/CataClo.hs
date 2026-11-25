-- catas whose algebra uses run-time locals (Resolve's validateVariables:
-- getDirectDeps), at functors with and without lists, at Fix and Cofree
{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module CataClo where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import qualified Data.Map as Map
import qualified Data.Set as Set

data F r = V Int | L Int r | A r r | Let [(Int, r)] r | M [r]
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Cofree F Int

deps :: [(Int, T)] -> Map.Map Int (Set.Set Int)
deps bs =
  let names = Set.fromList (fst <$> bs)
      direct = Set.toList . cata alg where
        alg = \case
          _ C.:< V n -> if Set.member n names then Set.singleton n else Set.empty
          _ C.:< L v body -> Set.delete v body
          _ C.:< A f x -> f <> x
          _ C.:< Let binds body ->
            let bound = Set.fromList (fst <$> binds)
            in Set.union (foldMap snd binds Set.\\ bound) (body Set.\\ bound)
          _ C.:< M xs -> mconcat xs
  in Map.fromList [ (n, Set.fromList (direct d)) | (n, d) <- bs ]

exDeps :: Int -> Int -> [(Int, [Int])]
exDeps a b = map (\(k, s) -> (k, Set.toList s)) (Map.toList (deps
  [ (a, 0 :< A (0 :< V b) (0 :< L a (0 :< V a)))
  , (b, 0 :< Let [(a, 1 :< V 2)] (0 :< M [0 :< V a, 0 :< V 2, 0 :< V 3]))
  , (2, 0 :< V a) ]))

data E r = N Int | P r r | Neg r
  deriving (Eq, Show, Functor)

scaled :: Int -> Int -> Fix E -> Int
scaled k d = cata $ \case
  N n -> n * k + d
  P a b -> a + b
  Neg a -> d - a

total :: Int -> [Int] -> Int
total _ [] = 0
total k (y : ys) = scaled k y (Fix (P (Fix (N y)) (Fix (Neg (Fix (N k)))))) + total (k + y) ys

exTotal :: Int -> [Int] -> Int
exTotal k ys = total k ys
