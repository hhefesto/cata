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
import qualified Data.Foldable as F
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (..))
import Data.Functor.Foldable (cata)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
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
filter _pred [] = []
filter pred (x : xs)
  | pred x = x : filter pred xs
  | otherwise = filter pred xs

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
anyDefault p t = F.any p (toListDefault t)

allDefault :: forall t a. Foldable t => (a -> Bool) -> t a -> Bool
allDefault p t = F.all p (toListDefault t)

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
