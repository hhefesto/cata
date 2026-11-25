{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
-- a step a top def is the knot of (telomare's refinementCheckStep): steps on
-- steps, one of which runs a whole traversal of the others
module CheckKnot where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (Base, Corecursive, Recursive, cata, embed, project)

data TF r = Z | P r r | D Int r | L r | S r | V | E Int r r | A Int r | U Int r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Fix TF

transN :: (Base g ~ TF, Recursive g) => (TF g -> g) -> g -> g
transN f = c where
  c = f . c' . project
  c' = \case
    s@(D _ _) -> s
    x         -> fmap c x

basicN :: (Base g ~ TF, Recursive g, Corecursive g) => (TF g -> g) -> TF g -> g
basicN other = \case
  L x | P a _ <- project x -> a
  y@Z       -> embed y
  y@(P _ _) -> embed y
  x         -> other x

stuckN :: (Base g ~ TF, Recursive g, Corecursive g) => (TF g -> g) -> TF g -> g
stuckN other = \case
  S x | P f e <- project x, D _ d <- project f -> transN (basicN (stuckN other) . repl (project e)) d
  y@(D _ _) -> embed y
  x         -> other x
  where
  repl e = \case
    V  -> e
    x' -> x'

abortN :: (Base g ~ TF, Recursive g, Corecursive g) => (TF g -> g) -> TF g -> g
abortN other = \case
  L x | A n r <- project x -> embed (A n r)
  y@(A _ _) -> embed y
  x         -> other x

checkStep :: Int -> TF T -> T
checkStep fuel = basicN (stuckN (abortN (gateStep (sameStep handleOther)))) where
  step = checkStep fuel
  barrier = Fix . U 0
  gateStep other = \case
    L (Fix (E n l r)) -> switch n (step (L l)) (step (L r))
    x                 -> other x
  switch n l r
    | size l == size r && n > 1 = l
    | otherwise                 = barrier (Fix (E n l r))
  size = cata (\x -> 1 + sum x)
  sameStep other = \case
    S (Fix (E _ l r)) | size l == size r -> l
    x -> other x
  handleOther = \case
    U n r | n < fuel  -> step (A n r)
          | otherwise -> Fix (A fuel r)
    E n l r           -> Fix (E n l r)
    _                 -> error "checkStep unexpected"

checkGate :: Int -> T -> T -> T
checkGate fuel r c = case checkStep fuel (A 1 c) of
  Fix (A n _) -> Fix (A (n + 1) r)
  x           -> x

run :: Int -> T -> T
run fuel = transN (checkStep fuel)

exRun :: Int -> Int -> T
exRun fuel k = run fuel (Fix (P (Fix (S (Fix (P (Fix (D 1 (Fix (P (Fix (L (Fix V))) (Fix (U k (Fix V))))))) (Fix (P (Fix (E 2 (Fix Z) (Fix Z))) (Fix Z))))))) (Fix (L (Fix (E k (Fix (P (Fix Z) (Fix Z))) (Fix (A 3 (Fix Z)))))))))

runIn :: Int -> T -> T
runIn budget x = case go x of
  Fix (A _ r) -> checkGate most r x
  y           -> y
  where
  most = budget + 1
  go (Fix (L y)) = go y
  go y           = run most y
