-- | cata's model of base's list functions that run a function they are
-- given more than once: their definitions in base (GHC.List, and
-- Data.Foldable's instance at lists). The specialiser (bend/Spec.bend)
-- writes a call of one at a list as a call of this module's def, so that
-- it is the package's own code: rule 15 copies it at its known function
-- argument, the argument's free locals the copy's first parameters. Bend
-- takes a template only closed, and a function a def runs again is a
-- template; a lambda over a pattern's variable (foldl (\a b -> x :< ..))
-- is then code in a first-order def, its variable a parameter.
--
-- Bend is strict, so foldl' is foldl.
module Cata.Base where

import Prelude hiding (concatMap, foldl, foldl', foldr)

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x : xs) = f x (foldr f z xs)

-- | the list first, so that each recursive call passes the function
-- unchanged and a shorter list (Bend's termination check reads the
-- arguments left to right)
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z0 xs0 = go xs0 z0
  where
    go [] z = z
    go (x : xs) z = go xs (f z x)

foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f z0 xs0 = go xs0 z0
  where
    go [] z = z
    go (x : xs) z = go xs (f z x)

-- | a list comprehension's generator (Spec writes [e | p <- l, Q] as
-- concatMap (\p -> [e | Q]) l)
concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f [] = []
concatMap f (x : xs) = f x ++ concatMap f xs
