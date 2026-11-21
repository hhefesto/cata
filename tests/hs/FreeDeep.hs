{-# LANGUAGE DeriveTraversable #-}
module FreeDeep where

-- Resolve's freeVarsDeep in its shape: cata with a where-bound algebra,
-- foldMap over a case's alternatives with a lambda over a local function
-- (patRefs, itself a cata whose algebra calls freeD back through a
-- pattern's annotation), F.fold for the rest.

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import qualified Data.Foldable as F
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import qualified Data.Set as Set

data PF r = PVar String | PPair r r | PAnn r Term
  deriving (Functor, Foldable, Traversable)

data EF r = EVar String | ELam String r | EApp r r | ECase r [(Fix PF, r)]
  deriving (Functor, Foldable, Traversable)

type Term = Cofree EF Int

freeD :: Term -> Set.Set String
freeD = cata alg where
  alg (_ C.:< EVar n) = Set.singleton n
  alg (_ C.:< ELam n body) = Set.delete n body
  alg (_ C.:< ECase scrut alts) = scrut <> foldMap (\(p, body) -> patRefs p <> body) alts <> caseRefs
    where
      caseRefs = Set.fromList ["and", "foldl"]
  alg e = F.fold e

  patRefs :: Fix PF -> Set.Set String
  patRefs = cata palg where
    palg :: PF (Set.Set String) -> Set.Set String
    palg (PAnn inner ty) = inner <> freeD ty
    palg e = F.fold e

pvar :: String -> Fix PF
pvar n = Fix (PVar n)

term :: String -> Term
term s = foldr (\w t -> 1 :< EApp (2 :< EVar w) t) (3 :< ECase (4 :< EVar "x") alts) (words s)
  where
    alts = [ (Fix (PPair (pvar "a") (Fix (PAnn (pvar "b") (5 :< EVar "ty")))), 6 :< ELam "a" (7 :< EVar "q"))
           , (pvar s, 8 :< EVar s) ]

ex1 :: String -> [String]
ex1 s = Set.toList (freeD (term s))

ex2 :: String -> [String]
ex2 s = Set.toList (freeD (9 :< ELam s (term s)))
