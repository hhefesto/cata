{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE LambdaCase        #-}
-- a tower of steps that calls itself, its last step partial, one step
-- written with local functions over the step itself
module GateStep where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data TF r = Z | P r r | L r | R r | S r | G r r | B r | A Int r | I Int | U Int r r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Fix TF

eqT :: T -> T -> Bool
eqT (Fix x) (Fix y) = case (x, y) of
  (Z, Z)           -> True
  (P a b, P c d)   -> eqT a c && eqT b d
  (G a b, G c d)   -> eqT a c && eqT b d
  (B a, B c)       -> eqT a c
  (A n a, A m c)   -> n == m && eqT a c
  (I n, I m)       -> n == m
  _                -> False

isD :: T -> Bool
isD = cata (\x -> case x of { Z -> True; P a b -> a && b; _ -> False })

basic :: (TF T -> T) -> TF T -> T
basic other = \case
  L (Fix (P a _)) -> a
  L (Fix Z)       -> Fix Z
  R (Fix (P _ b)) -> b
  x@Z             -> Fix x
  x@(P _ _)       -> Fix x
  x               -> other x

abortS :: (TF T -> T) -> TF T -> T
abortS other = \case
  L a@(Fix (A _ _))   -> a
  A o m | not (isD m) -> Fix (A o (Fix Z))
  x@(A _ _)           -> Fix x
  x                   -> other x

idx :: Int -> (TF T -> T) -> TF T -> T
idx n other = \case
  I m | m == n -> Fix Z
  x            -> other x

gate :: Int -> Int -> T -> T -> T
gate fuel o r c = case r of
  Fix Z           -> aborted
  a@(Fix (A _ _)) -> a
  Fix (P _ _)     -> c
  _               -> Fix (B (Fix (G aborted r)))
  where aborted = check fuel (A o (Fix (P (Fix Z) c)))

check :: Int -> TF T -> T
check fuel = basic (abortS (gs (same (idx 0 handleOther)))) where
  step = check fuel
  barrier = Fix . B
  gs other = \case
    L (Fix (B (Fix (G l r)))) -> switch (step (L l)) (step (L r)) r
    S (Fix (B (Fix (G l r)))) -> switch (step (S l)) (step (S r)) r
    x                         -> other x
  switch l r s
    | eqT l r && free s = l
    | otherwise        = barrier (Fix (G l r))
  free = cata (\case
    A _ _ -> False
    x     -> and x)
  same other = \case
    G (Fix (B a)) b | eqT a b && free b -> a
    x -> other x
  handleOther = \case
    G a b    -> barrier (Fix (G a b))
    U o tc c -> gate fuel o (app tc c) c
    S a      -> if fuel > 0 then a else Fix Z
    other    -> error ("check: unexpected" ++ show (const 1 other :: Int))
  app tc c = step . S . step $ P c tc

exCheck :: Int -> T
exCheck n = check n (U 3 (Fix (P (Fix Z) (Fix Z))) (Fix (P (Fix (I 1)) (Fix Z))))
