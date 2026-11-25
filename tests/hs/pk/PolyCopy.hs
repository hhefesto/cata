-- methods and model functions at types with variables of the def's own
-- (Desugar's patternToTerm, Surface's patternBinders, Resolve's i2t)
{-# LANGUAGE DeriveTraversable #-}
module PolyCopy where

import Control.Comonad.Cofree (Cofree (..))
import Control.Comonad.Trans.Cofree (CofreeF)
import qualified Control.Comonad.Trans.Cofree as CF
import Data.Fix (Fix (..))
import Data.Foldable (fold)
import Data.Functor.Foldable (ana, cata)
import Debug.Trace (trace)

data B r = Z | Pr r r
  deriving (Eq, Show, Functor, Foldable, Traversable)

class Basic f where
  embedB :: B r -> f r

data U c p r = UB (B r) | UI Int | UC c p r
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Basic (U c p) where
  embedB = UB

data P t r = PV String | PI Int | PP r r | PT t r
  deriving (Eq, Show, Functor, Foldable, Traversable)

binders :: Fix (P t) -> [String]
binders = cata alg where
  alg p = case p of
    PV s -> [s]
    q -> fold q

toTerm :: Int -> Fix (P t) -> Cofree (U c p) Int
toTerm n = cata alg where
  alg p = case p of
    PP a b -> n :< embedB (Pr a b)
    PI i -> n :< UI i
    PV _ -> n :< embedB Z
    PT _ a -> a

i2t :: a -> Int -> Cofree (U l v) a
i2t a = ana coalg where
  coalg n = a CF.:< (if n < 1 then embedB Z else embedB (Pr (n - 1) 0))

pat :: Int -> Fix (P Bool)
pat n = Fix (PP (Fix (PV "x")) (Fix (PT True (Fix (PP (Fix (PI n)) (Fix (PV "y")))))))

size :: Cofree (U () Int) Int -> Int
size (k :< u) = k + case u of
  UB Z -> 1
  UB (Pr a b) -> size a + 2 * size b
  UI i -> i
  UC _ m a -> m + size a

dbg :: String -> a -> a
dbg _ x = x

exBinders :: Int -> [String]
exBinders n = binders (pat n)

exTerm :: Int -> Int
exTerm n = size (toTerm 3 (pat n)) + size (i2t 2 (if n > 4 then 2 else n))

exDbg :: Int -> Int
exDbg n = dbg "f" (+ 1) (dbg "x" n) + dbg "g" negate n
