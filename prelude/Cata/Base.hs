{-# LANGUAGE ExplicitForAll #-}

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

import Control.Comonad.Trans.Cofree (CofreeF (..))

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

-- | iterate f x !! n, base's two definitions together (Spec writes the one
-- as the other): f applied n times to x, the infinite list never built.
-- A negative n is (!!)'s error.
iterateIndex :: (a -> a) -> a -> Int -> a
iterateIndex f x n
  | n < 0 = error "Prelude.!!: negative index"
  | n == 0 = x
  | otherwise = iterateIndex f (f x) (n - 1)

-- | base's instances at pairs, (,) w: Functor, Applicative (at a Monoid
-- w) and Traversable. Spec writes a method at (,) w as the def here, at w
-- then the method's types, and g <$> y <*> x as pairLiftA2 g y x (no pair
-- then holds a function).
pairFmap :: forall w a b. (a -> b) -> (w, a) -> (w, b)
pairFmap f (w, a) = (w, f a)

pairPure :: forall w a. Monoid w => a -> (w, a)
pairPure a = (mempty, a)

pairAp :: forall w a b. Monoid w => (w, a -> b) -> (w, a) -> (w, b)
pairAp (u, f) (v, x) = (u <> v, f x)

pairLiftA2 :: forall w a b c. Monoid w => (a -> b -> c) -> (w, a) -> (w, b) -> (w, c)
pairLiftA2 f (u, x) (v, y) = (u <> v, f x y)

pairTraverse :: forall w f a b. Applicative f => (a -> f b) -> (w, a) -> f (w, b)
pairTraverse f (w, a) = fmap (\b -> (w, b)) (f a)

-- | Control.Monad's Kleisli compositions (Spec writes f <=< g and f >=> g
-- as these), base's definitions: copied at their known functions, at the
-- monad's own >>=.
kleisliR :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
kleisliR f g x = g x >>= f

kleisliL :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
kleisliL f g x = f x >>= g

-- | free's instances at CofreeF f a (a Cofree's layer): Functor and
-- Traversable, its definitions (the annotation kept, the layer mapped).
-- Spec writes a method at CofreeF f a as the def here, at f and a then the
-- method's types; sequence and sequenceA are traverse id (the layer's
-- own traverse, the package's instance).
cofreeFFmap :: forall f a b c. Functor f => (b -> c) -> CofreeF f a b -> CofreeF f a c
cofreeFFmap g (a :< fb) = a :< fmap g fb

cofreeFTraverse :: forall f a g b c. (Traversable f, Applicative g) => (b -> g c) -> CofreeF f a b -> g (CofreeF f a c)
cofreeFTraverse h (a :< fb) = fmap (a :<) (traverse h fb)

cofreeFSequence :: forall f a g b. (Traversable f, Applicative g) => CofreeF f a (g b) -> g (CofreeF f a b)
cofreeFSequence (a :< fgb) = fmap (a :<) (traverse id fgb)
