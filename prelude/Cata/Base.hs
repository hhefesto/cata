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

import Prelude hiding (concatMap, filter, foldl, foldl', foldr, until)

import Control.Comonad.Trans.Cofree (CofreeF (..))
import qualified Data.Foldable as F
import Data.Fix (Fix (..))
import Data.Functor.Classes (Show1 (..))
import Data.Functor.Foldable (cata)
import GHC.Show (showList__)

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

-- | free's Foldable at CofreeF f a: foldr over the layer, the annotation
-- left out (Spec writes foldr at CofreeF f a as this def)
cofreeFFoldr :: forall f a b c. Foldable f => (b -> c -> c) -> c -> CofreeF f a b -> c
cofreeFFoldr g z (_ :< fb) = F.foldr g z fb

-- | Data.Foldable's fold (foldMap id) at any Foldable t: foldr (<>) mempty,
-- the same value at a lawful Monoid (Spec writes fold as this def, at t and
-- the Monoid)
foldMonoid :: forall t m. (Foldable t, Monoid m) => t m -> m
foldMonoid xs = F.foldr (<>) mempty xs

-- | Data.Foldable's foldMap at any Foldable t: its default, foldr (mappend
-- . f) mempty (Spec writes foldMap as this def, at t, the Monoid and the
-- element; a known f is copied in, its free locals the copy's parameters)
foldMapMonoid :: forall t m a. (Foldable t, Monoid m) => (a -> m) -> t a -> m
foldMapMonoid f xs = F.foldr (\x acc -> f x <> acc) mempty xs

-- | Data.Foldable's default foldr (base's $dmfoldr, which GHC's derived
-- Foldable leaves in place at a type whose variable is phantom, as
-- telomare's AbortableF): foldr over the elements foldMap gives as a list
-- (Spec writes $dmfoldr at t as this def; the same value, base's is
-- appEndo (foldMap (Endo . f) t) z)
foldrDefault :: forall t a b. Foldable t => (a -> b -> b) -> b -> t a -> b
foldrDefault f z t = foldr f z (F.foldMap (\x -> [x]) t)

-- | data-fix's Show instance at Fix f, through f's Show1: showsPrec d (Fix
-- a) is showParen (d >= 11) (showString "Fix " . liftShowsPrec showsPrec
-- showList 11 a), showList base's default (showList__ (showsPrec 0)). Spec
-- writes a method at Fix f (and shows) as the def here, at f. A node's
-- text at any precedence is its text unparenthesised, parenthesised from
-- 11 on, so this is a fold to that text: its children's showsPrec q is
-- fixShowsAt q of their text (exact when f's liftShowsPrec only prepends
-- text, as one built with base's Show combinators does; the laws hold it
-- to GHC's). The fold needs f's Functor too.
fixShowsAt :: Int -> String -> ShowS
fixShowsAt q s = showParen (q >= 11) (showString s)

fixShowAlg :: forall f. Show1 f => f String -> String
fixShowAlg a = showString "Fix " (liftShowsPrec fixShowsAt (showList__ showString) 11 a "")

fixShowsPrec :: forall f. (Functor f, Show1 f) => Int -> Fix f -> ShowS
fixShowsPrec d x = fixShowsAt d (cata fixShowAlg x)

fixShow :: forall f. (Functor f, Show1 f) => Fix f -> String
fixShow x = cata fixShowAlg x

fixShows :: forall f. (Functor f, Show1 f) => Fix f -> ShowS
fixShows x = showString (cata fixShowAlg x)

fixShowList :: forall f. (Functor f, Show1 f) => [Fix f] -> ShowS
fixShowList xs = showList__ showString (map (cata fixShowAlg) xs)

-- | base's until (GHC.Base's definition): f applied until p holds. Spec
-- writes until as this def; Bend sees no argument shrink, so the fold
-- writes it with fuel, as the bend branch writes such loops (README,
-- "Recursion Bend refuses: fuel").
until :: forall a. (a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x then x else until p f (f x)

-- | GHC.List's filter (Spec writes filter as this def, so that a known
-- predicate over a local, as Resolve's (`Set.member` reachable) . fst, is
-- copied in, the local the copy's parameter)
filter :: forall a. (a -> Bool) -> [a] -> [a]
filter _pred [] = []
filter pred (x : xs)
  | pred x = x : filter pred xs
  | otherwise = filter pred xs
