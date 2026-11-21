{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module FoldM where

-- cata's rule for Data.Foldable's fold: Base's model's foldMonoid (foldr
-- (<>) mempty) at the container, free's Foldable at CofreeF as the model's
-- cofreeFFoldr. The shapes are telomare's: IR.Surface's patternBinders (a
-- list), Resolve's freeVarsDeep (a Set, through a Cofree's layer), Size's
-- buildUnsizedLocMap (a Map), Resolve's validateVariables (a list of Sets)
-- and pruneBindings (a Map of Sets).

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import qualified Data.Foldable as F
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import qualified Data.Map as Map
import qualified Data.Set as Set

data PF r = PVar String | PPair r r | PLit Int
  deriving (Functor, Foldable, Traversable)

binders :: Fix PF -> [String]
binders = cata $ \case
  PVar n -> [n]
  p -> F.fold p

pat :: String -> Fix PF
pat [] = Fix (PLit 0)
pat (c : cs) = Fix (PPair (Fix (PVar [c])) (pat cs))

ex1 :: String -> [String]
ex1 s = binders (pat s)

data EF r = EVar String | ELam String r | EApp r r
  deriving (Functor, Foldable, Traversable)

type E = Cofree EF Int

var :: Int -> String -> E
var a n = a :< EVar n

lam :: Int -> String -> E -> E
lam a n b = a :< ELam n b

app :: Int -> E -> E -> E
app a f x = a :< EApp f x

free :: E -> Set.Set String
free = cata alg where
  alg (_ C.:< EVar n) = Set.singleton n
  alg (_ C.:< ELam n b) = Set.delete n b
  alg e = F.fold e

term :: String -> String -> E
term v w = lam 1 v (app 2 (app 3 (var 4 v) (var 5 w)) (var 6 "z"))

ex2 :: String -> String -> [String]
ex2 v w = Set.toList (free (term v w))

locs :: E -> Map.Map String Int
locs = cata f where
  f (a C.:< g) = case g of
    EVar n -> Map.singleton n a
    x -> F.fold x

ex3 :: String -> String -> [(String, Int)]
ex3 v w = Map.toList (locs (term v w))

ex4 :: [String] -> [String]
ex4 ws = Set.toList (F.fold (map (Set.fromList . words) ws))

ex5 :: String -> String -> [String]
ex5 a b = Set.toList (F.fold (Map.fromList [(1 :: Int, Set.fromList (words a)), (2, Set.fromList (words b))]))
