{-# LANGUAGE PatternSynonyms, ViewPatterns, TypeFamilies, LambdaCase, FlexibleInstances, DeriveTraversable, FlexibleContexts #-}
module Cls where

-- cata's spec pass: user classes, their instances (one with a context),
-- constrained functions, pattern synonyms over them (views included), as
-- telomare's IR.Base writes them

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as CofreeT
import Data.Fix (Fix (..))
import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))

data BasicExprF f = ZeroSF | PairSF f f
  deriving (Eq, Show, Functor, Foldable, Traversable)

class BasicBase g where
  embedB :: BasicExprF x -> g x
  extractB :: g x -> Maybe (BasicExprF x)

instance BasicBase BasicExprF where
  embedB = id
  extractB = pure

instance BasicBase f => BasicBase (CofreeT.CofreeF f Int) where
  embedB = (0 CofreeT.:<) . embedB
  extractB = extractB . (\(_ CofreeT.:< x) -> x)

pattern BasicFW :: BasicBase g => BasicExprF x -> g x
pattern BasicFW x <- (extractB -> Just x) where
  BasicFW x = embedB x

pattern GFix :: (Recursive g, Corecursive g, Base g ~ f) => f g -> g
pattern GFix x <- (project -> x) where
  GFix x = embed x

pattern BasicEE :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => BasicExprF g -> g
pattern BasicEE x = GFix (BasicFW x)

pattern ZeroB :: (Recursive g, Corecursive g, Base g ~ f, BasicBase f) => g
pattern ZeroB = BasicEE ZeroSF

pattern PairB :: (Recursive g, Corecursive g, Base g ~ f, BasicBase f) => g -> g -> g
pattern PairB a b = BasicEE (PairSF a b)

type BasicExpr = Fix BasicExprF

type Tagged = Cofree BasicExprF Int

size :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => g -> Int
size = \case
  ZeroB -> 1
  PairB a b -> size a + size b
  _ -> 0

build :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => [Int] -> g
build [] = ZeroB
build (_ : xs) = PairB (build xs) ZeroB

sizeFix :: [Int] -> Int
sizeFix xs = size (build xs :: BasicExpr)

sizeTagged :: [Int] -> Int
sizeTagged xs = size (build xs :: Tagged)

leftmost :: BasicExpr -> Bool
leftmost = \case
  PairB ZeroB _ -> True
  _ -> False

class Pretty a where
  pretty :: a -> String

instance Pretty Bool where
  pretty True = "yes"
  pretty False = "no"

instance Pretty a => Pretty [a] where
  pretty = concatMap pretty

twice :: Pretty a => a -> String
twice x = pretty x ++ pretty x

prettyBools :: [Bool] -> String
prettyBools bs = twice bs
