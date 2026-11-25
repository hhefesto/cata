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

import Control.Applicative (Alternative (..))
import qualified Control.Applicative as A
import Control.Comonad.Trans.Cofree (CofreeF (..))
import qualified Control.Comonad.Cofree as C
import Control.Exception (Exception)
import Control.Monad.State (State, get, gets, modify, put)
import Data.Char (chr, ord)
import qualified Data.Foldable as F
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (..))
import Data.Functor.Foldable (cata)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word (Word8)
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
  | otherwise = iterateTimes f x n

-- | f applied n times to x: x is f's argument at the bottom, so that at an
-- action (a function) no argument grows
iterateTimes :: (a -> a) -> a -> Int -> a
iterateTimes f x n
  | n <= 0 = x
  | otherwise = f (iterateTimes f x (n - 1))

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

-- | Data.Foldable's asum, base's definition: foldr (<|>) empty (Spec writes
-- asum at t f a as this def; its foldr is the Foldable's at t, a package's
-- derived instance's own code, its <|> and empty the Alternative's at f)
asum :: forall t f a. (F.Foldable t, Alternative f) => t (f a) -> f a
asum xs = F.foldr (<|>) empty xs

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

-- | free's Show instance at Cofree f a, through f's Show1 and a's Show:
-- showsPrec d (a :< as) is showParen (d > 5) (showsPrec 6 a . showString
-- " :< " . liftShowsPrec showsPrec showList 5 as), as a fold to a node's
-- unparenthesised text (as fixShow's).
cofreeShowsAt :: Int -> String -> ShowS
cofreeShowsAt q s = showParen (q >= 6) (showString s)

cofreeShowAlg :: forall f a. (Show1 f, Show a) => CofreeF f a String -> String
cofreeShowAlg (a :< as) = showsPrec 6 a (showString " :< " (liftShowsPrec cofreeShowsAt (showList__ showString) 5 as ""))

cofreeShowsPrec :: forall f a. (Functor f, Show1 f, Show a) => Int -> C.Cofree f a -> ShowS
cofreeShowsPrec d x = cofreeShowsAt d (cata cofreeShowAlg x)

cofreeShow :: forall f a. (Functor f, Show1 f, Show a) => C.Cofree f a -> String
cofreeShow x = cata cofreeShowAlg x

cofreeShows :: forall f a. (Functor f, Show1 f, Show a) => C.Cofree f a -> ShowS
cofreeShows x = showString (cata cofreeShowAlg x)

cofreeShowList :: forall f a. (Functor f, Show1 f, Show a) => [C.Cofree f a] -> ShowS
cofreeShowList xs = showList__ showString (map (cata cofreeShowAlg) xs)

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
filter pred ys = case ys of
  [] -> []
  x : xs -> if pred x then x : filter pred xs else filter pred xs

-- | GHC.Show's showsPrec at Maybe, a list and a pair, given showsPrec at the
-- parts (Spec's sp.shw writes it so at one of the package's types): a type
-- that holds a Maybe of itself (telomare's LocTag) shows it by a copy that
-- calls its own showsPrec, not by a template given it.
showMaybeWith :: forall a. (Int -> a -> ShowS) -> Int -> Maybe a -> ShowS
showMaybeWith sp d m s = case m of
  Nothing -> showString "Nothing" s
  Just x -> showParen (d >= 11) (\r -> showString "Just " (sp 11 x r)) s

showListWith :: forall a. (Int -> a -> ShowS) -> Int -> [a] -> ShowS
showListWith sp d [] s = '[' : ']' : s
showListWith sp d (x : xs) s = '[' : sp 0 x (showListRest sp xs s)

showListRest :: forall a. (Int -> a -> ShowS) -> [a] -> ShowS
showListRest sp [] s = ']' : s
showListRest sp (y : ys) s = ',' : sp 0 y (showListRest sp ys s)

showPairWith :: forall a b. (Int -> a -> ShowS) -> (Int -> b -> ShowS) -> Int -> (a, b) -> ShowS
showPairWith sp sq d (a, b) s = '(' : sp 0 a (',' : sq 0 b (')' : s))

-- | base's monadic list functions, its definitions, at a monad cata's
-- prelude has none for (Identity, ReaderT, WriterT, a StateT over another
-- monad, the package's own): Spec writes traverse, mapM, forM, for, mapM_,
-- forM_, traverse_, for_, foldM, sequence and sequenceA at a list as these,
-- at the monad then the method's types (sp.pc.ltab).
listTraverse :: forall f a b. Applicative f => (a -> f b) -> [a] -> f [b]
listTraverse f [] = pure []
listTraverse f (x : xs) = liftA2 (:) (f x) (listTraverse f xs)

listFor :: forall f a b. Applicative f => [a] -> (a -> f b) -> f [b]
listFor xs f = listTraverse f xs

listMapM :: forall m a b. Monad m => (a -> m b) -> [a] -> m [b]
listMapM f [] = pure []
listMapM f (x : xs) = f x >>= \y -> fmap (y :) (listMapM f xs)

listForM :: forall m a b. Monad m => [a] -> (a -> m b) -> m [b]
listForM xs f = listMapM f xs

listTraverse_ :: forall f a b. Applicative f => (a -> f b) -> [a] -> f ()
listTraverse_ f [] = pure ()
listTraverse_ f (x : xs) = liftA2 (\_ u -> u) (f x) (listTraverse_ f xs)

listFor_ :: forall f a b. Applicative f => [a] -> (a -> f b) -> f ()
listFor_ xs f = listTraverse_ f xs

listMapM_ :: forall m a b. Monad m => (a -> m b) -> [a] -> m ()
listMapM_ f [] = pure ()
listMapM_ f (x : xs) = f x >>= \_ -> listMapM_ f xs

listForM_ :: forall m a b. Monad m => [a] -> (a -> m b) -> m ()
listForM_ xs f = listMapM_ f xs

listFoldM :: forall m b a. Monad m => (b -> a -> m b) -> b -> [a] -> m b
listFoldM f z [] = pure z
listFoldM f z (x : xs) = f z x >>= \y -> listFoldM f y xs

listSequenceA :: forall f a. Applicative f => [f a] -> f [a]
listSequenceA [] = pure []
listSequenceA (x : xs) = liftA2 (:) x (listSequenceA xs)

listSequence :: forall m a. Monad m => [m a] -> m [a]
listSequence [] = pure []
listSequence (x : xs) = x >>= \y -> fmap (y :) (listSequence xs)

-- | base's Traversable at Maybe
maybeTraverse :: forall f a b. Applicative f => (a -> f b) -> Maybe a -> f (Maybe b)
maybeTraverse f Nothing = pure Nothing
maybeTraverse f (Just x) = fmap Just (f x)

maybeSequenceA :: forall f a. Applicative f => Maybe (f a) -> f (Maybe a)
maybeSequenceA Nothing = pure Nothing
maybeSequenceA (Just x) = fmap Just x

-- | base's Semigroup and Monoid at Maybe
maybeAppend :: forall a. Semigroup a => Maybe a -> Maybe a -> Maybe a
maybeAppend Nothing b = b
maybeAppend a Nothing = a
maybeAppend (Just a) (Just b) = Just (a <> b)

maybeMempty :: forall a. Maybe a
maybeMempty = Nothing

-- | Data.Foldable's defaults at a package's own Foldable (a derived one has
-- its foldr; toList and foldl' are the class's defaults)
toListDefault :: forall t a. Foldable t => t a -> [a]
toListDefault t = F.foldr (:) [] t

foldlDefault :: forall t b a. Foldable t => (b -> a -> b) -> b -> t a -> b
foldlDefault f z t = foldl f z (toListDefault t)

-- | Data.Foldable's sum, product and length at a package's functor, through
-- its elements (base's definitions at such a Foldable).
sumDefault :: forall t a. (Foldable t, Num a) => t a -> a
sumDefault t = F.sum (toListDefault t)

productDefault :: forall t a. (Foldable t, Num a) => t a -> a
productDefault t = F.product (toListDefault t)

lengthDefault :: forall t a. Foldable t => t a -> Int
lengthDefault t = F.length (toListDefault t)

-- | free's unwrap (ComonadCofree's) at Cofree: the layer under the
-- annotation (the instance's Functor f, unused, makes a call of it a copy
-- at its f, as the model's other defs are)
unwrapCofree :: forall f a. Functor f => C.Cofree f a -> f (C.Cofree f a)
unwrapCofree (_ C.:< x) = x

-- | GHC.Show's shows at a package's own type: base's definition, so that
-- the specialiser writes it at the type's own showsPrec (a derived one's)
showsDefault :: forall a. Show a => a -> ShowS
showsDefault x = showsPrec 0 x

-- | base's functions over a Functor, a Monad or a Foldable that are no
-- methods, at a package's own: base's definitions, so that the specialiser
-- writes them at its instance's methods.
fmapOp :: forall f a b. Functor f => (a -> b) -> f a -> f b
fmapOp g x = fmap g x

fmapFlip :: forall f a b. Functor f => f a -> (a -> b) -> f b
fmapFlip x g = fmap g x

bindFlip :: forall m a b. Monad m => (a -> m b) -> m a -> m b
bindFlip k m = m >>= k

voidOp :: forall f a. Functor f => f a -> f ()
voidOp x = fmap (\_ -> ()) x

whenOp :: forall f. Applicative f => Bool -> f () -> f ()
whenOp b x = if b then x else pure ()

unlessOp :: forall f. Applicative f => Bool -> f () -> f ()
unlessOp b x = if b then pure () else x

liftM2Op :: forall m a b r. Monad m => (a -> b -> r) -> m a -> m b -> m r
liftM2Op f m n = m >>= \x -> n >>= \y -> pure (f x y)

anyDefault :: forall t a. Foldable t => (a -> Bool) -> t a -> Bool
anyDefault p t = anyList p (toListDefault t)

allDefault :: forall t a. Foldable t => (a -> Bool) -> t a -> Bool
allDefault p t = allList p (toListDefault t)

orDefault :: forall t. Foldable t => t Bool -> Bool
orDefault t = F.or (toListDefault t)

andDefault :: forall t. Foldable t => t Bool -> Bool
andDefault t = F.and (toListDefault t)

nullDefault :: forall t a. Foldable t => t a -> Bool
nullDefault t = F.null (toListDefault t)

elemDefault :: forall t a. (Foldable t, Eq a) => a -> t a -> Bool
elemDefault x t = F.elem x (toListDefault t)

concatMapDefault :: forall t a b. Foldable t => (a -> [b]) -> t a -> [b]
concatMapDefault f t = concatMap f (toListDefault t)

concatDefault :: forall t a. Foldable t => t [a] -> [a]
concatDefault t = F.concat (toListDefault t)

-- | the classes' default methods at a package's own instance
thenOp :: forall m a b. Monad m => m a -> m b -> m b
thenOp m k = m >>= \_ -> k

returnOp :: forall m a. Monad m => a -> m a
returnOp x = pure x

mapMOp :: forall t m a b. (Traversable t, Monad m) => (a -> m b) -> t a -> m (t b)
mapMOp f t = traverse f t

sequenceOp :: forall t m a. (Traversable t, Monad m) => t (m a) -> m (t a)
sequenceOp t = traverse (\x -> x) t

constMap :: forall f a b. Functor f => a -> f b -> f a
constMap x t = fmap (\_ -> x) t

-- | data-fix's Eq at Fix f: base's Eq1 at f, its liftEq (the package's
-- instance) at the recursion
fixEq :: forall f. Eq1 f => Fix f -> Fix f -> Bool
fixEq (Fix a) (Fix b) = liftEq fixEq a b

fixNe :: forall f. Eq1 f => Fix f -> Fix f -> Bool
fixNe a b = not (fixEq a b)

-- | Control.Exception's throw of a package's own exception: a failure value
-- with what it shows (the message of a Haskell error call)
throwOp :: forall a e. Exception e => e -> a
throwOp x = errorWithoutStackTrace (show x)

-- | Foldable's foldMap, traverse_ and for_ at Maybe
maybeFoldMap :: forall m a. Monoid m => (a -> m) -> Maybe a -> m
maybeFoldMap f t = case t of
  Nothing -> mempty
  Just x -> f x

maybeTraverse_ :: forall f a b. Applicative f => (a -> f b) -> Maybe a -> f ()
maybeTraverse_ f t = case t of
  Nothing -> pure ()
  Just x -> fmap (\_ -> ()) (f x)

maybeFor_ :: forall f a b. Applicative f => Maybe a -> (a -> f b) -> f ()
maybeFor_ t f = case t of
  Nothing -> pure ()
  Just x -> fmap (\_ -> ()) (f x)

-- | f <$> a <*> b <*> c at a package's own Applicative
liftA3Op :: forall m a b c d. Applicative m => (a -> b -> c -> d) -> m a -> m b -> m c -> m d
liftA3Op g a b c = A.liftA2 (\p z -> case p of (x, y) -> g x y z) (A.liftA2 (\x y -> (x, y)) a b) c

-- | Data.List's partition, its function a known argument
partition :: forall a. (a -> Bool) -> [a] -> ([a], [a])
partition p xs = case xs of
  [] -> ([], [])
  y : ys -> case partition p ys of
    (ts, fs) -> if p y then (y : ts, fs) else (ts, y : fs)

-- | Data.List's break and span, their function a known argument
breakOp :: forall a. (a -> Bool) -> [a] -> ([a], [a])
breakOp p xs = case xs of
  [] -> ([], [])
  y : ys -> if p y then ([], y : ys) else case breakOp p ys of
    (ts, fs) -> (y : ts, fs)

spanOp :: forall a. (a -> Bool) -> [a] -> ([a], [a])
spanOp p xs = case xs of
  [] -> ([], [])
  y : ys -> if p y then (case spanOp p ys of (ts, fs) -> (y : ts, fs)) else ([], y : ys)

-- | containers' partition at Set and Map, Map's mapMaybe (its pairs, in
-- order), Data.Function's on
setPartition :: forall a. Ord a => (a -> Bool) -> Set.Set a -> (Set.Set a, Set.Set a)
setPartition p s = case partition p (Set.toAscList s) of
  (ts, fs) -> (Set.fromList ts, Set.fromList fs)

mapPartition :: forall a k. (a -> Bool) -> Map.Map k a -> (Map.Map k a, Map.Map k a)
mapPartition p m = case partitionPairs p (Map.toAscList m) of
  (ts, fs) -> (Map.fromDistinctAscList ts, Map.fromDistinctAscList fs)

partitionPairs :: forall a k. (a -> Bool) -> [(k, a)] -> ([(k, a)], [(k, a)])
partitionPairs p xs = case xs of
  [] -> ([], [])
  (k, v) : t -> case partitionPairs p t of
    (ts, fs) -> if p v then ((k, v) : ts, fs) else (ts, (k, v) : fs)

mapMapMaybe :: forall a b k. (a -> Maybe b) -> Map.Map k a -> Map.Map k b
mapMapMaybe f m = Map.fromDistinctAscList (mapMaybePairs f (Map.toAscList m))

mapMaybePairs :: forall a b k. (a -> Maybe b) -> [(k, a)] -> [(k, b)]
mapMaybePairs f xs = case xs of
  [] -> []
  (k, v) : t -> case f v of
    Nothing -> mapMaybePairs f t
    Just w -> (k, w) : mapMaybePairs f t

onOp :: forall b c a. (b -> b -> c) -> (a -> b) -> a -> a -> c
onOp f g x y = f (g x) (g y)

-- | containers' unionWithKey: the first's pairs put in the second, at a key
-- of both the function's (a known function is copied in, so it may be
-- partial, as Resolve's DeferMap's is)
unionWithKeyOp :: forall k a. Ord k => (k -> a -> a -> a) -> Map.Map k a -> Map.Map k a -> Map.Map k a
unionWithKeyOp f a b = unionPairs f (Map.toAscList a) b

unionPairs :: forall k a. Ord k => (k -> a -> a -> a) -> [(k, a)] -> Map.Map k a -> Map.Map k a
unionPairs f xs b = case xs of
  [] -> b
  (k, v) : t -> insertPair f k v (unionPairs f t b)

insertPair :: forall k a. Ord k => (k -> a -> a -> a) -> k -> a -> Map.Map k a -> Map.Map k a
insertPair f k v m = case Map.lookup k m of
  Nothing -> Map.insert k v m
  Just w -> Map.insert k (f k v w) m

-- | Foldable's functions at Maybe
maybeNull :: forall a. Maybe a -> Bool
maybeNull t = case t of
  Nothing -> True
  Just _ -> False

maybeAny :: forall a. (a -> Bool) -> Maybe a -> Bool
maybeAny p t = case t of
  Nothing -> False
  Just x -> p x

maybeAll :: forall a. (a -> Bool) -> Maybe a -> Bool
maybeAll p t = case t of
  Nothing -> True
  Just x -> p x

maybeElem :: forall a. Eq a => a -> Maybe a -> Bool
maybeElem x t = case t of
  Nothing -> False
  Just y -> x == y

maybeToListF :: forall a. Maybe a -> [a]
maybeToListF t = case t of
  Nothing -> []
  Just x -> [x]

maybeLength :: forall a. Maybe a -> Int
maybeLength t = case t of
  Nothing -> 0
  Just _ -> 1

maybeFoldr :: forall a b. (a -> b -> b) -> b -> Maybe a -> b
maybeFoldr f z t = case t of
  Nothing -> z
  Just x -> f x z

maybeConcatMap :: forall a b. (a -> [b]) -> Maybe a -> [b]
maybeConcatMap f t = case t of
  Nothing -> []
  Just x -> f x

-- | containers' IntMap (!): its own error text, not Map's
intMapAt :: forall a. IntMap.IntMap a -> Int -> a
intMapAt m k = case IntMap.lookup k m of
  Just v -> v
  Nothing -> error ("IntMap.!: key " ++ show k ++ " is not an element of the map")

-- | containers' mapKeys: fromList of the pairs, the greatest old key kept
-- where two map to one
mapKeys :: forall k2 k1 a. Ord k2 => (k1 -> k2) -> Map.Map k1 a -> Map.Map k2 a
mapKeys f m = Map.fromList (map (\(k, x) -> (f k, x)) (Map.toList m))

-- | recursion-schemes' ana at free's Cofree f l and at data-fix's Fix f
-- (base's definition, embed . fmap (ana g) . g): fuel, as any recursion
-- Bend sees nothing shrink in
anaCofree :: forall f l a. Functor f => (a -> CofreeF f l a) -> a -> C.Cofree f l
anaCofree g x = case g x of
  l :< fx -> l C.:< fmap (\y -> anaCofree g y) fx

anaFix :: forall f a. Functor f => (a -> f a) -> a -> Fix f
anaFix g x = Fix (fmap (\y -> anaFix g y) (g x))

-- | lens's transform at free's Cofree f l (its Plated instance there is the
-- Traversable's children), the children first
transformCofree :: forall f l. Functor f => (C.Cofree f l -> C.Cofree f l) -> C.Cofree f l -> C.Cofree f l
transformCofree g (l C.:< fx) = g (l C.:< fmap (\y -> transformCofree g y) fx)

-- | GHC.Show's default showsPrec (an instance that defines show)
showsPrecDefault :: forall a. (a -> String) -> Int -> a -> ShowS
showsPrecDefault sh _ x s = sh x ++ s

-- | IO, read as the state of what a program sees of the world: its
-- console's input not read yet, its output so far, its files (a file of
-- bytes is their characters). Spec writes the type IO as State World and
-- base's console and file actions as the ones here, so that IO's binds are
-- State's; an action that throws (the end of the input, a file that is not
-- there) is a partial one. What the model leaves out (other handles,
-- exceptions caught, processes, time, randomness) stays IO, and out.
data World = World String String (Map.Map String String)

ioPutStr :: String -> State World ()
ioPutStr s = modify (\w -> case w of World i o f -> World i (o ++ s) f)

ioPutStrLn :: String -> State World ()
ioPutStrLn s = ioPutStr (s ++ "\n")

ioPutChar :: Char -> State World ()
ioPutChar c = ioPutStr [c]

ioPrint :: forall a. Show a => a -> State World ()
ioPrint x = ioPutStr (show x ++ "\n")

worldLine :: World -> Maybe (String, World)
worldLine (World i o f) = case i of
  [] -> Nothing
  _ -> case break (== '\n') i of
    (l, r) -> Just (l, World (drop 1 r) o f)

ioGetLine :: State World String
ioGetLine = do
  w <- get
  case worldLine w of
    Nothing -> error "<stdin>: hGetLine: end of file"
    Just (l, v) -> put v >> pure l

worldChar :: World -> Maybe (Char, World)
worldChar (World i o f) = case i of
  [] -> Nothing
  c : r -> Just (c, World r o f)

ioGetChar :: State World Char
ioGetChar = do
  w <- get
  case worldChar w of
    Nothing -> error "<stdin>: hGetChar: end of file"
    Just (c, v) -> put v >> pure c

worldIn :: World -> (String, World)
worldIn (World i o f) = (i, World [] o f)

ioGetContents :: State World String
ioGetContents = do
  w <- get
  case worldIn w of
    (i, v) -> put v >> pure i

ioInteract :: (String -> String) -> State World ()
ioInteract f = ioGetContents >>= \s -> ioPutStr (f s)

worldEOF :: World -> Bool
worldEOF (World i o f) = null i

ioIsEOF :: State World Bool
ioIsEOF = gets worldEOF

worldFile :: String -> World -> Maybe String
worldFile p (World i o f) = Map.lookup p f

ioReadFile :: String -> State World String
ioReadFile p = do
  w <- get
  case worldFile p w of
    Nothing -> error (p ++ ": openFile: does not exist (No such file or directory)")
    Just s -> pure s

ioWriteFile :: String -> String -> State World ()
ioWriteFile p s = modify (\w -> case w of World i o f -> World i o (Map.insert p s f))

ioAppendFile :: String -> String -> State World ()
ioAppendFile p s = modify (\w -> case w of World i o f -> World i o (Map.insert p (Map.findWithDefault [] p f ++ s) f))

-- | a file's bytes
ioReadBytes :: String -> State World [Word8]
ioReadBytes p = fmap (map (\c -> fromIntegral (ord c))) (ioReadFile p)

ioWriteBytes :: String -> [Word8] -> State World ()
ioWriteBytes p bs = ioWriteFile p (map (\b -> chr (fromIntegral b)) bs)

-- | the handle of the output, and its flush
ioStdout :: ()
ioStdout = ()

ioFlush :: () -> State World ()
ioFlush _ = pure ()

-- | base's Down: the order the other way round
newtype Down a = Down a

instance Eq a => Eq (Down a) where
  Down x == Down y = x == y

instance Ord a => Ord (Down a) where
  compare (Down x) (Down y) = compare y x

getDown :: Down a -> a
getDown (Down x) = x

-- | base's comparing and sortOn at a key that is a Down (their definitions;
-- sortOn's keys are computed once each in base's)
comparingOp :: forall a b. Ord a => (b -> a) -> b -> b -> Ordering
comparingOp f x y = compare (f x) (f y)

sortOnOp :: forall b a. Ord b => (a -> b) -> [a] -> [a]
sortOnOp f xs = sortByOp (\x y -> compare (f x) (f y)) xs

-- | foldr (.) id (intersperse s (map f xs)): no list of functions
composeSep :: forall a. ShowS -> (a -> ShowS) -> [a] -> ShowS
composeSep s f xs r = case xs of
  [] -> r
  [y] -> f y r
  y : ys -> f y (s (composeSep s f ys r))

-- | sequence of a list written out: no list of actions
sequence1 :: forall m a. Monad m => m a -> m [a]
sequence1 a = a >>= \x -> pure [x]

sequence2 :: forall m a. Monad m => m a -> m a -> m [a]
sequence2 a b = a >>= \x -> b >>= \y -> pure [x, y]

sequence3 :: forall m a. Monad m => m a -> m a -> m a -> m [a]
sequence3 a b c = a >>= \x -> b >>= \y -> c >>= \z -> pure [x, y, z]

sequence4 :: forall m a. Monad m => m a -> m a -> m a -> m a -> m [a]
sequence4 a b c d = a >>= \x -> b >>= \y -> c >>= \z -> d >>= \u -> pure [x, y, z, u]

sequence5 :: forall m a. Monad m => m a -> m a -> m a -> m a -> m a -> m [a]
sequence5 a b c d e = a >>= \x -> b >>= \y -> c >>= \z -> d >>= \u -> e >>= \v -> pure [x, y, z, u, v]

-- | Data.List's sortBy (a stable merge sort), and minimumBy, maximumBy,
-- groupBy and nubBy at lists: at a function over run-time locals, which a
-- template of the prelude's could not take
sortByOp :: forall a. (a -> a -> Ordering) -> [a] -> [a]
sortByOp cmp xs = sortRuns cmp (map (\x -> [x]) xs)

sortRuns :: forall a. (a -> a -> Ordering) -> [[a]] -> [a]
sortRuns cmp rs = case rs of
  [] -> []
  [r] -> r
  a : b : t -> sortRuns cmp (mergePairs cmp (a : b : t))

mergePairs :: forall a. (a -> a -> Ordering) -> [[a]] -> [[a]]
mergePairs cmp rs = case rs of
  a : b : t -> mergeBy cmp a b : mergePairs cmp t
  t -> t

mergeBy :: forall a. (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy cmp xs ys = case xs of
  [] -> ys
  x : xt -> case ys of
    [] -> x : xt
    y : yt -> case cmp x y of
      GT -> y : mergeBy cmp (x : xt) yt
      _ -> x : mergeBy cmp xt (y : yt)

minimumByOp :: forall a. (a -> a -> Ordering) -> [a] -> a
minimumByOp cmp xs = case xs of
  [] -> error "minimumBy: empty structure"
  x : t -> minimumGo cmp x t

minimumGo :: forall a. (a -> a -> Ordering) -> a -> [a] -> a
minimumGo cmp x ys = case ys of
  [] -> x
  y : t -> minimumGo cmp (case cmp x y of { GT -> y; _ -> x }) t

maximumByOp :: forall a. (a -> a -> Ordering) -> [a] -> a
maximumByOp cmp xs = case xs of
  [] -> error "maximumBy: empty structure"
  x : t -> maximumGo cmp x t

maximumGo :: forall a. (a -> a -> Ordering) -> a -> [a] -> a
maximumGo cmp x ys = case ys of
  [] -> x
  y : t -> maximumGo cmp (case cmp x y of { GT -> x; _ -> y }) t

groupByOp :: forall a. (a -> a -> Bool) -> [a] -> [[a]]
groupByOp eq xs = case xs of
  [] -> []
  x : t -> case spanBy eq x t of
    (ys, zs) -> (x : ys) : groupByOp eq zs

spanBy :: forall a. (a -> a -> Bool) -> a -> [a] -> ([a], [a])
spanBy eq x ys = case ys of
  [] -> ([], [])
  y : t -> if eq x y then (case spanBy eq x t of (as, bs) -> (y : as, bs)) else ([], y : t)

nubByOp :: forall a. (a -> a -> Bool) -> [a] -> [a]
nubByOp eq xs = nubGo eq xs []

nubGo :: forall a. (a -> a -> Bool) -> [a] -> [a] -> [a]
nubGo eq ys xs = case ys of
  [] -> []
  y : t -> if elemBy eq y xs then nubGo eq t xs else y : nubGo eq t (y : xs)

elemBy :: forall a. (a -> a -> Bool) -> a -> [a] -> Bool
elemBy eq y xs = case xs of
  [] -> False
  x : t -> eq x y || elemBy eq y t

minimumOnOp :: forall b a. Ord b => (a -> b) -> [a] -> a
minimumOnOp f xs = minimumByOp (\x y -> compare (f x) (f y)) xs

maximumOnOp :: forall b a. Ord b => (a -> b) -> [a] -> a
maximumOnOp f xs = maximumByOp (\x y -> compare (f x) (f y)) xs

-- | Set's filter and map at a function over run-time locals
setFilterOp :: forall a. Ord a => (a -> Bool) -> Set.Set a -> Set.Set a
setFilterOp p s = Set.fromList (filter p (Set.toAscList s))

setMapOp :: forall b a. Ord b => (a -> b) -> Set.Set a -> Set.Set b
setMapOp f s = Set.fromList (mapList f (Set.toAscList s))

mapList :: forall a b. (a -> b) -> [a] -> [b]
mapList f xs = case xs of
  [] -> []
  x : t -> f x : mapList f t

-- | the one-element monoid
unitAppend :: () -> () -> ()
unitAppend a b = ()

unitMempty :: ()
unitMempty = ()

-- | first and second at a pair that holds a function
firstPair :: forall a b c. (a -> b) -> (a, c) -> (b, c)
firstPair f p = case p of (a, c) -> (f a, c)

secondPair :: forall b c a. (b -> c) -> (a, b) -> (a, c)
secondPair f p = case p of (a, b) -> (a, f b)

-- | base's Const: m, whatever the other type says (Spec writes base's as this
-- one)
newtype Const m a = Const { getConst :: m }

instance Functor (Const m) where
  fmap _ (Const v) = Const v

instance Monoid m => Applicative (Const m) where
  pure _ = Const mempty
  liftA2 _ (Const x) (Const y) = Const (x <> y)
  Const x <*> Const y = Const (x <> y)

-- | containers' mergeWithKey: f at the keys in both, g and h the rest of each
-- (what its documentation asks of g and h: each answers a part of its map)
mergeWithKeyOp :: forall k a b c. Ord k => (k -> a -> b -> Maybe c) -> (Map.Map k a -> Map.Map k c) -> (Map.Map k b -> Map.Map k c) -> Map.Map k a -> Map.Map k b -> Map.Map k c
mergeWithKeyOp f g h a b =
  Map.union (Map.fromDistinctAscList (mergeKeyed f b (Map.toList a)))
            (Map.union (g (Map.difference a b)) (h (Map.difference b a)))

mergeKeyed :: forall k a b c. Ord k => (k -> a -> b -> Maybe c) -> Map.Map k b -> [(k, a)] -> [(k, c)]
mergeKeyed f b [] = []
mergeKeyed f b ((k, x) : r) = case Map.lookup k b of
  Nothing -> mergeKeyed f b r
  Just y  -> mergeKeep k (f k x y) (mergeKeyed f b r)

mergeKeep :: forall k c. k -> Maybe c -> [(k, c)] -> [(k, c)]
mergeKeep k Nothing r  = r
mergeKeep k (Just z) r = (k, z) : r

-- | containers' foldlWithKey and foldlWithKey' (Bend is strict)
mapFoldlWithKey :: forall a k b. (a -> k -> b -> a) -> a -> Map.Map k b -> a
mapFoldlWithKey f z m = foldlPairs f (Map.toList m) z

foldlPairs :: forall a k b. (a -> k -> b -> a) -> [(k, b)] -> a -> a
foldlPairs f [] z            = z
foldlPairs f ((k, x) : xs) z = foldlPairs f xs (f z k x)

setDisjoint :: forall a. Ord a => Set.Set a -> Set.Set a -> Bool
setDisjoint a b = Set.null (Set.intersection a b)

-- | containers' foldl and foldl' at a Set, void at a Map
setFoldl :: forall a b. (a -> b -> a) -> a -> Set.Set b -> a
setFoldl f z s = foldl f z (Set.toAscList s)

mapVoid :: forall k a. Map.Map k a -> Map.Map k ()
mapVoid m = Map.map (\_ -> ()) m


-- | x, or Nothing where x errs (cata reads it so: an error is a failure value;
-- in Haskell an error is an error)
attempt :: forall a. a -> Maybe a
attempt x = Just x

-- | x with its error, if it errs, kept for where it is read (cata: the failure
-- value itself)
holdE :: forall a. a -> Either String a
holdE x = Right x

readE :: forall a. Either String a -> a
readE (Right x) = x
readE (Left m)  = error m

-- | the Map m that is m = Map.mapWithKey (g m) d: g's lookups in it are
-- knotLookup's and knotFind's, an error at a key of d with no answer yet. By
-- rounds: a key whose answer errs waits for the next; when a round adds none,
-- its error is the Map's (GHC's <<loop>> when the keys wait on each other)
knotLookup :: forall k a b. Ord k => Map.Map k a -> Map.Map k b -> k -> Maybe b
knotLookup d m h = case Map.lookup h m of
  Just v  -> Just v
  Nothing -> if Map.member h d then error "<<loop>>" else Nothing

knotFind :: forall k a b. Ord k => Map.Map k a -> Map.Map k b -> b -> k -> b
knotFind d m e h = case knotLookup d m h of
  Just v  -> v
  Nothing -> e

mapKnot :: forall k a b. Ord k => (Map.Map k b -> k -> a -> b) -> Map.Map k a -> Map.Map k b
mapKnot g d = knotRounds g (Map.toList d) (Map.toList d) Map.empty

knotRounds :: forall k a b. Ord k => (Map.Map k b -> k -> a -> b) -> [(k, a)] -> [(k, a)] -> Map.Map k b -> Map.Map k b
knotRounds g [] todo done = knotStuck g todo done
knotRounds g (_ : fuel) todo done = case knotPass g todo done of
  (done', rest) -> if length rest == length todo then knotStuck g rest done' else knotRounds g fuel rest done'

knotPass :: forall k a b. Ord k => (Map.Map k b -> k -> a -> b) -> [(k, a)] -> Map.Map k b -> (Map.Map k b, [(k, a)])
knotPass g [] done = (done, [])
knotPass g ((k, x) : r) done = case attempt (g done k x) of
  Just v  -> knotPass g r (Map.insert k v done)
  Nothing -> knotKeep k x (knotPass g r done)

knotKeep :: forall k a b. k -> a -> (Map.Map k b, [(k, a)]) -> (Map.Map k b, [(k, a)])
knotKeep k x (m, r) = (m, (k, x) : r)

knotStuck :: forall k a b. Ord k => (Map.Map k b -> k -> a -> b) -> [(k, a)] -> Map.Map k b -> Map.Map k b
knotStuck g [] done = done
knotStuck g ((k, x) : r) done = knotStuck g r (Map.insert k (g done k x) done)

-- | containers' traverseWithKey, and Foldable's foldMap at a Map
mapTraverseWithKey :: forall t k a b. Applicative t => (k -> a -> t b) -> Map.Map k a -> t (Map.Map k b)
mapTraverseWithKey f m = fmap Map.fromDistinctAscList (traversePairs f (Map.toList m))

traversePairs :: forall t k a b. Applicative t => (k -> a -> t b) -> [(k, a)] -> t [(k, b)]
traversePairs f []            = pure []
traversePairs f ((k, x) : xs) = A.liftA2 (\y ys -> (k, y) : ys) (f k x) (traversePairs f xs)

mapFoldMap :: forall k m a. Monoid m => (a -> m) -> Map.Map k a -> m
mapFoldMap f m = foldMapElems f (Map.elems m)

foldMapElems :: forall m a. Monoid m => (a -> m) -> [a] -> m
foldMapElems f []       = mempty
foldMapElems f (x : xs) = f x <> foldMapElems f xs

-- | (,) w's Monad
pairBind :: forall w a b. Monoid w => (w, a) -> (a -> (w, b)) -> (w, b)
pairBind p k = case p of
  (u, x) -> case k x of
    (v, y) -> (u <> v, y)

-- | free's <$ at a Cofree: every annotation replaced
cofreeConst :: forall f a b. Functor f => a -> C.Cofree f b -> C.Cofree f a
cofreeConst x = cata (\(_ :< g) -> x C.:< g)

-- | base's mconcat (at a Map)
mconcatOp :: forall m. Monoid m => [m] -> m
mconcatOp []       = mempty
mconcatOp (x : xs) = x <> mconcatOp xs

-- | base's any and all at a list, their recursion (a p that calls back the def
-- it is in, EAL's closedTerm, is then a group's member)
anyList :: forall a. (a -> Bool) -> [a] -> Bool
anyList p xs = case xs of
  [] -> False
  x : t -> if p x then True else anyList p t

allList :: forall a. (a -> Bool) -> [a] -> Bool
allList p xs = case xs of
  [] -> True
  x : t -> if p x then allList p t else False
