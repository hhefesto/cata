-- a cata at an algebra over a pattern's variable (Machine's superStepM:
-- cata (filterLeft n))
{-# LANGUAGE DeriveFunctor #-}
module CataPat where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data U r = Sup (Maybe Int) r r | Lf Int | Nd r r
  deriving (Eq, Show, Functor)

type T = Fix U

step :: T -> T
step (Fix u) = case u of
  Nd (Fix (Sup n a b)) e ->
    let fl = if null n then id else cata (filterLeft n)
        fr = if null n then id else cata (filterRight n)
    in Fix (Nd (fl e) (Fix (Nd (fr e) a)))
  Sup n a b -> cata (filterLeft n) (Fix (Nd a b))
  x -> Fix x
  where
  filterLeft :: Maybe Int -> U T -> T
  filterLeft n x = case x of
    Sup m a _ | m == n -> a
    y -> Fix y
  filterRight n x = case x of
    Sup m _ b | m == n -> b
    y -> Fix y

size :: T -> Int
size (Fix u) = case u of
  Sup n a b -> maybe 0 id n + 10 * size a + size b
  Lf n -> n
  Nd a b -> 1 + size a + 2 * size b

exStep :: Int -> Int
exStep n = size (step (Fix (Nd (Fix (Sup (Just n) (Fix (Lf 1)) (Fix (Lf 2)))) (Fix (Sup (Just 2) (Fix (Lf n)) (Fix (Lf 4)))))))
