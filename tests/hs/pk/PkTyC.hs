-- functions at Data.Map's, Data.Set's, Fix's and Cofree's types, over the
-- module PkTyA's types
module PkTyC where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Fix (Fix (..))
import Control.Comonad.Cofree (Cofree (..))
import PkTyA

sizePlus :: Map.Map Int Int -> Int
sizePlus m = Map.size m + sum (Map.elems m)

lookTag :: Int -> Map.Map Int Tag -> Maybe Tag
lookTag k m = Map.lookup k m

putTag :: Int -> Tag -> Map.Map Int Tag -> Map.Map Int Tag
putTag k t m = Map.insert k t m

names :: Map.Map String Int -> [String]
names m = Map.keys m

setUp :: Set.Set Int -> [Int]
setUp s = map (\x -> x + 1) (Set.toList s)

addSet :: Int -> Set.Set Int -> Set.Set Int
addSet x s = Set.insert x s

evalE :: Fix ExprF -> Int
evalE (Fix e) = case e of
  Lit n -> n
  Add a b -> evalE a + evalE b
  Neg a -> 0 - evalE a

negE :: Fix ExprF -> Fix ExprF
negE (Fix e) = case e of
  Lit n -> Fix (Lit (0 - n))
  Add a b -> Fix (Add (negE a) (negE b))
  Neg a -> a

annSum :: Cofree ExprF Int -> Int
annSum (a :< e) = case e of
  Lit n -> a + n
  Add l r -> a + annSum l + annSum r
  Neg l -> a - annSum l
