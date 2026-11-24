-- BendRt: the Haskell meaning of the Bend names cata's output uses, for
-- bend2hs (bend/Back.bend): G maps cata's Bend back to Haskell, and a name
-- that is Base's or the prelude's (List.append, HsPrelude.HsList.foldr,
-- hs.eq.list) becomes b' and the name with its dots as primes, defined
-- here, its type arguments erased (G drops them) and its other arguments
-- in Bend's order.  Each is Base's or the prelude's definition, by
-- Haskell's own function where they agree (Nat is a non-negative Int:
-- cata writes Int as Nat only where nothing goes below zero; Nat.sub is
-- Base's, which stops at 0).  A name G needs and this lacks is GHC's
-- "not in scope", which tests/back/run.zsh reports by module.
{-# LANGUAGE NoMonomorphismRestriction, PatternSynonyms, ViewPatterns, TypeFamilies, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
module BendRt
  ( module BendRt
  , module BendPc
  , Bool (..), Maybe (..), Either (..), Ordering (..), Int, Integer, Natural, Char, String, Float, IO, Rational
  , (.), ($)
  ) where

import Prelude
import BendPc
import Data.Ratio ((%), numerator, denominator)
import qualified Data.Char as DC
import Numeric.Natural (Natural)
import Data.List (genericLength, genericTake, genericDrop, genericReplicate, sortBy, nubBy, isPrefixOf, isSuffixOf, isInfixOf, intercalate, intersperse, groupBy, insertBy, tails, inits, partition, stripPrefix)
import Data.Maybe (mapMaybe, catMaybes, isJust, isNothing, listToMaybe, maybeToList)
import Data.Either (lefts, rights, partitionEithers, isLeft, isRight, fromLeft, fromRight)
import Data.Bits ((.&.), (.|.), xor, complement, shiftR, shiftL, rotateR)
import Data.Word (Word32, Word64)

-- Bend's types (G writes B' and the name)
type B'Nat = Int
type B'U32 = Int
type B'Bool = Bool
type B'Char = Char
type B'String = [Char]
type B'Unit = ()
type B'Cmp = Ordering
type B'List a = [a]
type B'Maybe a = Maybe a
type B'Either a b = Either a b
type B'Sigma a b = (a, b)
type B'F32 = Float
-- cata's prelude's Int and Integer (HsPrelude.HsInt) is Haskell's: Pos n is
-- n, Neg n is -n (n at least 1), as BendRt's pattern synonyms
type B'HsPrelude'HsInt = Int

-- what G could not write
b'todo :: a
b'todo = error "bend2hs: a form G does not write"

-- a Nat pattern 1n+p
b'pred :: Integral a => a -> Maybe a
b'pred n = if n >= 1 then Just (n - 1) else Nothing

b'chr :: Integral a => a -> Char
b'chr = toEnum . fromIntegral

-- cata's prelude: an if with thunks
b'Bool'if c t e = if c then t () else e ()

b'Bool'and a b = a && b
b'Bool'or a b = a || b
b'Bool'not = not
b'Bool'xor a b = a /= b
b'Bool'is_eq a b = a == (b :: Bool)
b'Bool'pick c a b = if c then a else b

b'Nat'add a b = a + b
b'Nat'sub a b = if a < b then 0 else a - b
b'Nat'mul a b = a * b
b'Nat'div a b = if b == 0 then 0 else a `div` b
b'Nat'mod a b = if b == 0 then a else a `mod` b
b'Nat'pow a b = a ^ b
-- Nat's comparisons and show are a number's (Num beside Eq, Ord or Show):
-- G(F(h)) uses them at h's Int, Integer or Natural, and F(G(b)) reads
-- them at Integer by the Report's default rule (Survey's sv.dfl), as Nat's
b'Nat'max :: (Ord a, Num a) => a -> a -> a
b'Nat'max a b = max a b
b'Nat'min :: (Ord a, Num a) => a -> a -> a
b'Nat'min a b = min a b
b'Nat'is_eq :: (Eq a, Num a) => a -> a -> Bool
b'Nat'is_eq a b = a == b
-- a def's dictionaries at h's type (Fold's fd.dc)
b'dict'eq :: Eq a => a -> a -> Bool
b'dict'eq = (==)
b'dict'cmp :: Ord a => a -> a -> Ordering
b'dict'cmp = compare
b'Nat'is_ne :: (Eq a, Num a) => a -> a -> Bool
b'Nat'is_ne a b = a /= b
b'Nat'is_lt :: (Ord a, Num a) => a -> a -> Bool
b'Nat'is_lt a b = a < b
b'Nat'is_le :: (Ord a, Num a) => a -> a -> Bool
b'Nat'is_le a b = a <= b
b'Nat'is_gt :: (Ord a, Num a) => a -> a -> Bool
b'Nat'is_gt a b = a > b
b'Nat'is_ge :: (Ord a, Num a) => a -> a -> Bool
b'Nat'is_ge a b = a >= b
b'Nat'cmp :: (Ord a, Num a) => a -> a -> Ordering
b'Nat'cmp a b = compare a b
b'Nat'show :: (Show a, Num a) => a -> String
b'Nat'show n = show n
-- Bend's 1n+n (G writes a successor that is no pattern so), by Haskell's
-- succ: F reads succ at a number back as 1n+n
b'Nat'succ :: Enum a => a -> a
b'Nat'succ n = succ n
b'Nat'pred n = if n <= 0 then 0 else n - 1
b'Nat'is_zero n = n == 0

b'Char'is_eq a b = a == (b :: Char)
b'Char'cmp a b = compare a (b :: Char)
b'Char'to_u32 c = DC.ord c
b'Char'from_u32 n = DC.chr n
b'Char'is_digit = DC.isDigit
b'Char'to_upper = DC.toUpper
b'Char'to_lower = DC.toLower

b'String'to_list :: String -> [Char]
b'String'to_list s = s
b'String'from_list :: [Char] -> String
b'String'from_list s = s
b'String'eq a b = a == (b :: String)
b'String'append a b = a ++ (b :: String)

b'Cmp'is_eq o = o == EQ
b'Cmp'is_lt o = o == LT
b'Cmp'is_gt o = o == GT
b'Cmp'is_le c = c /= GT
b'Cmp'is_ge c = c /= LT

b'List'append xs ys = xs ++ ys
b'List'length xs = genericLength xs
b'List'reverse = reverse
-- Base's List is Haskell's list, its Maybe Maybe, cata's Either Either:
-- the wrappers at them, not at any Foldable or Monad (F reads a class's
-- method at a type variable as out)
b'List'concat :: [[a]] -> [a]
b'List'concat = concat
b'List'map f xs = map f xs
b'List'filter f xs = filter f xs
b'List'any :: (a -> Bool) -> [a] -> Bool
b'List'any f xs = any f xs
b'List'all :: (a -> Bool) -> [a] -> Bool
b'List'all f xs = all f xs
b'List'take xs n = genericTake n xs
b'List'drop xs n = genericDrop n xs
b'List'replicate n x = genericReplicate n x
b'List'contains :: (a -> a -> Bool) -> [a] -> a -> Bool
b'List'contains eq xs x = any (eq x) xs
b'List'foldr :: (a -> b -> b) -> [a] -> b -> b
b'List'foldr f xs z = foldr f z xs
b'List'foldl :: (b -> a -> b) -> [a] -> b -> b
b'List'foldl f xs z = foldl f z xs
b'List'is_empty :: [a] -> Bool
b'List'is_empty = null
b'List'head xs = listToMaybe xs
b'List'tail xs = drop 1 xs
b'List'last xs = if null xs then Nothing else Just (last xs)
b'List'zip xs ys = zip xs ys
b'List'sum :: Num a => [a] -> a
b'List'sum xs = sum xs

b'Maybe'map :: (a -> b) -> Maybe a -> Maybe b
b'Maybe'map f m = fmap f m
b'Maybe'bind :: Maybe a -> (a -> Maybe b) -> Maybe b
b'Maybe'bind m f = m >>= f
b'Maybe'default m d = maybe d id m

-- cata's module prelude (hs.*)
b'hs'map f xs = map f xs
b'hs'maybe d f m = maybe d f m
b'hs'either f g e = either f g e
b'hs'either'bind :: Either e a -> (a -> Either e b) -> Either e b
b'hs'either'bind m f = m >>= f
b'hs'either'map :: (a -> b) -> Either e a -> Either e b
b'hs'either'map f m = fmap f m
b'hs'eq'list eq xs ys = length xs == length ys && and (zipWith eq xs ys)
b'hs'eq'maybe eq a b = case (a, b) of
  (Nothing, Nothing) -> True
  (Just x, Just y) -> eq x y
  _ -> False
b'hs'eq'pair ea eb (a, b) (c, d) = ea a c && eb b d

-- HsPrelude's lists (HsPrelude.HsList.NAME)
b'HsPrelude'HsList'foldr :: (a -> b -> b) -> [a] -> b -> b
b'HsPrelude'HsList'foldr f xs z = foldr f z xs
b'HsPrelude'HsList'foldl :: (b -> a -> b) -> [a] -> b -> b
b'HsPrelude'HsList'foldl f xs z = foldl f z xs
b'HsPrelude'HsList'foldrc :: (a -> b -> b) -> [a] -> b -> b
b'HsPrelude'HsList'foldrc f xs z = foldr f z xs
b'HsPrelude'HsList'foldlc :: (b -> a -> b) -> [a] -> b -> b
b'HsPrelude'HsList'foldlc f xs z = foldl f z xs
b'HsPrelude'HsList'anyc :: (a -> Bool) -> [a] -> Bool
b'HsPrelude'HsList'anyc f xs = any f xs
b'HsPrelude'HsList'allc :: (a -> Bool) -> [a] -> Bool
b'HsPrelude'HsList'allc f xs = all f xs
b'HsPrelude'HsList'fst = fst
b'HsPrelude'HsList'snd = snd
b'HsPrelude'HsList'swap (a, b) = (b, a)
b'HsPrelude'HsList'uncurry = uncurry
b'HsPrelude'HsList'zip xs ys = zip xs ys
b'HsPrelude'HsList'zip3 xs ys zs = map (\(a, b, c) -> (a, (b, c))) (zip3 xs ys zs)
b'HsPrelude'HsList'zipWith f xs ys = zipWith f xs ys
b'HsPrelude'HsList'zipWith3 f xs ys zs = zipWith3 f xs ys zs
b'HsPrelude'HsList'unzip ps = unzip ps
b'HsPrelude'HsList'lookup eq k xs = case [v | (k', v) <- xs, eq k k'] of
  (v : _) -> Just v
  [] -> Nothing
b'HsPrelude'HsList'takeWhile p xs = takeWhile p xs
b'HsPrelude'HsList'dropWhile p xs = dropWhile p xs
b'HsPrelude'HsList'span p xs = span p xs
b'HsPrelude'HsList'break p xs = break p xs
b'HsPrelude'HsList'partition p xs = partition p xs
b'HsPrelude'HsList'find p xs = case filter p xs of
  (x : _) -> Just x
  [] -> Nothing
b'HsPrelude'HsList'elem :: (a -> a -> Bool) -> a -> [a] -> Bool
b'HsPrelude'HsList'elem eq x xs = any (eq x) xs
b'HsPrelude'HsList'notElem :: (a -> a -> Bool) -> a -> [a] -> Bool
b'HsPrelude'HsList'notElem eq x xs = not (any (eq x) xs)
b'HsPrelude'HsList'nub eq xs = nubBy eq xs
b'HsPrelude'HsList'nubBy eq xs = nubBy eq xs
b'HsPrelude'HsList'isPrefixOf eq xs ys = length xs <= length ys && and (zipWith eq xs ys)
b'HsPrelude'HsList'isSuffixOf eq xs ys = b'HsPrelude'HsList'isPrefixOf eq (reverse xs) (reverse ys)
b'HsPrelude'HsList'isInfixOf eq xs ys = any (b'HsPrelude'HsList'isPrefixOf eq xs) (tails ys)
b'HsPrelude'HsList'intersperse s xs = intersperse s xs
b'HsPrelude'HsList'intercalate s xss = intercalate s xss
b'HsPrelude'HsList'lines = lines
b'HsPrelude'HsList'unlines = unlines
b'HsPrelude'HsList'words = words
b'HsPrelude'HsList'unwords = unwords
b'HsPrelude'HsList'sortBy cmp xs = sortBy cmp xs
b'HsPrelude'HsList'sort cmp xs = sortBy cmp xs
b'HsPrelude'HsList'sortOn cmp f xs = sortBy (\a b -> cmp (f a) (f b)) xs
b'HsPrelude'HsList'insertBy cmp x xs = insertBy cmp x xs
b'HsPrelude'HsList'groupBy eq xs = groupBy eq xs
b'HsPrelude'HsList'group eq xs = groupBy eq xs
b'HsPrelude'HsList'tails xs = tails xs
b'HsPrelude'HsList'inits xs = inits xs
b'HsPrelude'HsList'mapMaybe f xs = mapMaybe f xs
b'HsPrelude'HsList'catMaybes xs = catMaybes xs
b'HsPrelude'HsList'isJust m = isJust m
b'HsPrelude'HsList'isNothing m = isNothing m
b'HsPrelude'HsList'listToMaybe xs = listToMaybe xs
b'HsPrelude'HsList'maybeToList m = maybeToList m
b'HsPrelude'HsList'lefts xs = lefts xs
b'HsPrelude'HsList'rights xs = rights xs
b'HsPrelude'HsList'partitionEithers xs = partitionEithers xs
b'HsPrelude'HsList'isLeft e = isLeft e
b'HsPrelude'HsList'isRight e = isRight e
b'HsPrelude'HsList'fromLeft d e = fromLeft d e
b'HsPrelude'HsList'fromRight d e = fromRight d e
b'HsPrelude'HsList'stripPrefix eq xs ys = if b'HsPrelude'HsList'isPrefixOf eq xs ys then Just (drop (length xs) ys) else Nothing
b'HsPrelude'HsList'toList xs = xs
b'HsPrelude'HsList'nil = []
b'HsPrelude'HsList'snoc xs x = xs ++ [x]

-- HsPrelude's show at Nat, Char, String, Bool (HsPrelude.HsShow.NAME)
b'HsPrelude'HsShow'string s r = s ++ r
b'HsPrelude'HsShow'char c r = c : r
b'HsPrelude'HsShow'space r = ' ' : r
b'HsPrelude'HsShow'commaSpace r = ',' : ' ' : r
b'HsPrelude'HsShow'paren b p r = if b then '(' : p (')' : r) else p r
b'HsPrelude'HsShow'digits n = show n
b'HsPrelude'HsShow'nat d n r = showsPrec d n r
b'HsPrelude'HsShow'bool b r = shows b r
b'HsPrelude'HsShow'unit u r = shows (u :: ()) r
b'HsPrelude'HsShow'str cs r = shows (cs :: String) r
b'HsPrelude'HsShow'litString cs r = init (tail (show (cs :: String))) ++ r
b'HsPrelude'HsShow'charq c r = shows (c :: Char) r

-- a module Main's main, which no law runs
b'main :: IO ()
b'main = return ()

-- Base's U32 (an Int below 2^32: cata writes a U32 for a character's code
-- and for a fuel bound) and F32 (a Float)
b'U32'to_nat n = fromIntegral (n :: Int)
b'U32'from_nat n = fromIntegral n :: Int
b'U32'is_eq a b = a == (b :: Int)
b'U32'is_ne a b = a /= (b :: Int)
b'U32'is_lt a b = a < (b :: Int)
b'U32'is_le a b = a <= (b :: Int)
b'U32'is_gt a b = a > (b :: Int)
b'U32'is_ge a b = a >= (b :: Int)
b'U32'cmp a b = compare a (b :: Int)

b'F32'add a b = a + (b :: Float)
b'F32'sub a b = a - (b :: Float)
b'F32'mul a b = a * (b :: Float)
b'F32'div a b = a / (b :: Float)
b'F32'min a b = min a (b :: Float)
b'F32'max a b = max a (b :: Float)
b'F32'is_eq a b = a == (b :: Float)
b'F32'is_ne a b = a /= (b :: Float)
b'F32'is_lt a b = a < (b :: Float)
b'F32'is_le a b = a <= (b :: Float)
b'F32'is_gt a b = a > (b :: Float)
b'F32'is_ge a b = a >= (b :: Float)
b'F32'from_nat n = fromIntegral n :: Float

-- the prelude's Haskell Int (HsPrelude.HsInt): Pos n and Neg n as views of
-- an Int; each operation as the prelude defines it (quot, rem, div and mod
-- by 0 are the prelude's total answers: Nat.div n 0 is 0, Nat.mod n 0 n)
b'posv :: (Ord a, Num a) => a -> Maybe a
b'posv k = if k >= 0 then Just k else Nothing
b'negv :: (Ord a, Num a) => a -> Maybe a
b'negv k = if k < 0 then Just (negate k) else Nothing
pattern B'HsPrelude'HsInt'Pos :: (Ord a, Num a) => a -> a
pattern B'HsPrelude'HsInt'Pos n <- (b'posv -> Just n) where B'HsPrelude'HsInt'Pos n = n
pattern B'HsPrelude'HsInt'Neg :: (Ord a, Num a) => a -> a
pattern B'HsPrelude'HsInt'Neg n <- (b'negv -> Just n) where B'HsPrelude'HsInt'Neg n = negate n
{-# COMPLETE B'HsPrelude'HsInt'Pos, B'HsPrelude'HsInt'Neg #-}

b'HsPrelude'HsInt'of n = n
b'HsPrelude'HsInt'neg'of n = negate n
b'HsPrelude'HsInt'negate a = negate a
b'HsPrelude'HsInt'nsub a b = a - b
b'HsPrelude'HsInt'add a b = a + b
b'HsPrelude'HsInt'sub a b = a - b
b'HsPrelude'HsInt'mul a b = a * b
b'HsPrelude'HsInt'abs a = abs a
b'HsPrelude'HsInt'signum a = signum a
b'HsPrelude'HsInt'mag a = abs a
b'HsPrelude'HsInt'isneg a = a < 0
b'HsPrelude'HsInt'cmp a b = compare a b
b'HsPrelude'HsInt'is_eq a b = a == b
b'HsPrelude'HsInt'is_ne a b = a /= b
b'HsPrelude'HsInt'is_lt a b = a < b
b'HsPrelude'HsInt'is_le a b = a <= b
b'HsPrelude'HsInt'is_gt a b = a > b
b'HsPrelude'HsInt'is_ge a b = a >= b
b'HsPrelude'HsInt'max a b = max a b
b'HsPrelude'HsInt'min a b = min a b
b'HsPrelude'HsInt'succ a = a + 1
b'HsPrelude'HsInt'pred a = a - 1
b'HsPrelude'HsInt'even a = even a
b'HsPrelude'HsInt'odd a = odd a
b'HsPrelude'HsInt'show a = show a
b'HsPrelude'HsInt'count a = max 0 a
b'HsPrelude'HsInt'mul'sign neg n = if neg then negate n else n
b'HsPrelude'HsInt'quot a b = b'HsPrelude'HsInt'mul'sign ((a < 0) /= (b < 0)) (b'Nat'div (abs a) (abs b))
b'HsPrelude'HsInt'rem a b = b'HsPrelude'HsInt'mul'sign (a < 0) (b'Nat'mod (abs a) (abs b))
b'HsPrelude'HsInt'div a b = let { q = b'HsPrelude'HsInt'quot a b; r = b'HsPrelude'HsInt'rem a b } in if r /= 0 && ((a < 0) /= (b < 0)) then q - 1 else q
b'HsPrelude'HsInt'mod a b = let r = b'HsPrelude'HsInt'rem a b in if r /= 0 && ((r < 0) /= (b < 0)) then r + b else r
b'HsPrelude'HsInt'pow a e = a ^ abs e
b'HsPrelude'HsInt'gcd a b = gcd a b
b'HsPrelude'HsInt'lcm a b = lcm a b
b'HsPrelude'HsInt'range a b = [a .. b]
b'HsPrelude'HsInt'rangeBy a b c = [a, b .. c]
-- (its elements' type its own: toInteger is nothing in F, and h's Int bounds
-- may list Integers)
b'HsPrelude'HsList'range :: (Integral a, Num b) => a -> a -> [b]
b'HsPrelude'HsList'range a b = map fromIntegral [a .. b]
b'HsPrelude'HsList'rangeBy :: (Integral a, Num b) => a -> a -> a -> [b]
b'HsPrelude'HsList'rangeBy a b c = map fromIntegral [a, b .. c]
b'HsPrelude'HsList'rangeChar a b = [a .. b]
b'HsPrelude'HsNum'even n = even n
b'HsPrelude'HsNum'odd n = odd n

-- the prelude's partial functions, each a failure value (Left GHC's
-- message) where GHC throws (bend/Prelude.bend, "Partial functions")
b'HsPrelude'HsList'error msg = Left msg
b'HsPrelude'HsList'undefined = Left "Prelude.undefined"
b'HsPrelude'HsList'head xs = case xs of { [] -> Left "Prelude.head: empty list"; (x : _) -> Right x }
b'HsPrelude'HsList'tail xs = case xs of { [] -> Left "Prelude.tail: empty list"; (_ : t) -> Right t }
b'HsPrelude'HsList'last xs = case xs of { [] -> Left "Prelude.last: empty list"; _ -> Right (last xs) }
b'HsPrelude'HsList'init xs = case xs of { [] -> Left "Prelude.init: empty list"; _ -> Right (init xs) }
b'HsPrelude'HsList'fromJust m = case m of { Nothing -> Left "Maybe.fromJust: Nothing"; Just x -> Right x }
b'maxgo :: (a -> a -> Ordering) -> a -> [a] -> a
b'maxgo cmp x t = foldl (\a b -> case cmp a b of { GT -> a; _ -> b }) x t
b'mingo :: (a -> a -> Ordering) -> a -> [a] -> a
b'mingo cmp x t = foldl (\a b -> case cmp a b of { GT -> b; _ -> a }) x t
b'HsPrelude'HsList'maximum cmp xs = case xs of { [] -> Left "Prelude.maximum: empty list"; (x : t) -> Right (b'maxgo cmp x t) }
b'HsPrelude'HsList'minimum cmp xs = case xs of { [] -> Left "Prelude.minimum: empty list"; (x : t) -> Right (b'mingo cmp x t) }
b'HsPrelude'HsList'maximumBy cmp xs = case xs of { [] -> Left "maximumBy: empty structure"; (x : t) -> Right (b'maxgo cmp x t) }
b'HsPrelude'HsList'minimumBy cmp xs = case xs of { [] -> Left "minimumBy: empty structure"; (x : t) -> Right (b'mingo cmp x t) }
b'HsPrelude'HsList'foldr1 f xs = case xs of { [] -> Left "Prelude.foldr1: empty list"; _ -> Right (foldr1 f xs) }
b'HsPrelude'HsList'foldl1 f xs = case xs of { [] -> Left "Prelude.foldl1: empty list"; _ -> Right (foldl1 f xs) }
b'HsPrelude'HsList'index xs n = if n < 0 then Left "Prelude.!!: negative index" else case genericDrop n xs of { [] -> Left "Prelude.!!: index too large"; (x : _) -> Right x }
-- xs !! n where Int is Nat (a module alone): n is never negative
b'HsPrelude'HsList'index'go xs n = b'HsPrelude'HsList'index xs n
-- div, mod, quot and rem by what may be 0 (HsNum: GHC's DivideByZero,
-- shown "divide by zero"); at Nat (non-negative) quot is div, rem mod
-- the list functions given a partial function (prelude/HsPartial.bend's HsPt)
b'HsPrelude'HsPt'bind m k = m >>= k
b'HsPrelude'HsPt'map :: (a -> Either String b) -> [a] -> Either String [b]
b'HsPrelude'HsPt'map f xs = mapM f xs
b'HsPrelude'HsPt'foldr :: (a -> b -> Either String b) -> [a] -> b -> Either String b
b'HsPrelude'HsPt'foldr f xs z = case xs of { [] -> Right z; (x : t) -> b'HsPrelude'HsPt'foldr f t z >>= \r -> f x r }
b'HsPrelude'HsPt'foldl :: (b -> a -> Either String b) -> [a] -> b -> Either String b
b'HsPrelude'HsPt'foldl f xs acc = case xs of { [] -> Right acc; (x : t) -> f acc x >>= \r -> b'HsPrelude'HsPt'foldl f t r }
b'HsPrelude'HsPt'filter :: (a -> Either String Bool) -> [a] -> Either String [a]
b'HsPrelude'HsPt'filter p xs = case xs of { [] -> Right []; (x : t) -> p x >>= \k -> (if k then (x :) else id) <$> b'HsPrelude'HsPt'filter p t }
b'HsPrelude'HsPt'any :: (a -> Either String Bool) -> [a] -> Either String Bool
b'HsPrelude'HsPt'any p xs = case xs of { [] -> Right False; (x : t) -> p x >>= \v -> if v then Right True else b'HsPrelude'HsPt'any p t }
b'HsPrelude'HsPt'all :: (a -> Either String Bool) -> [a] -> Either String Bool
b'HsPrelude'HsPt'all p xs = case xs of { [] -> Right True; (x : t) -> p x >>= \v -> if v then b'HsPrelude'HsPt'all p t else Right False }
b'HsPrelude'HsPt'zipWith :: (a -> b -> Either String c) -> [a] -> [b] -> Either String [c]
b'HsPrelude'HsPt'zipWith f xs ys = sequence (zipWith f xs ys)
b'HsPrelude'HsPt'mapMaybe :: (a -> Either String (Maybe b)) -> [a] -> Either String [b]
b'HsPrelude'HsPt'mapMaybe f xs = case xs of { [] -> Right []; (x : t) -> f x >>= \m -> maybe id (:) m <$> b'HsPrelude'HsPt'mapMaybe f t }
-- the partial binds at an answer that is no Data, and the monads' binds and
-- maps, maybe and either given a partial function (Fold's fd.pt.hoq, fd.pa)
b'HsPrelude'HsPt'bindq m k = m >>= k
b'HsPrelude'HsPt'exs'bind p f = case p of { (Left e, s) -> Right (Left e, s); (Right a, s) -> f a s }
b'HsPrelude'HsPt'exs'map f p = case p of { (Left e, s) -> Right (Left e, s); (Right a, s) -> f a >>= \b -> Right (Right b, s) }
b'HsPrelude'HsPt'state'bind p f = case p of { (a, s) -> f a s }
b'HsPrelude'HsPt'state'map f p = case p of { (a, s) -> f a >>= \b -> Right (b, s) }
b'HsPrelude'HsPt'either'bind m f = case m of { Left e -> Right (Left e); Right a -> f a }
b'HsPrelude'HsPt'either'map f m = case m of { Left e -> Right (Left e); Right a -> f a >>= \b -> Right (Right b) }
b'HsPrelude'HsPt'maybe'bind m f = case m of { Nothing -> Right Nothing; Just a -> f a }
b'HsPrelude'HsPt'maybe'map f m = case m of { Nothing -> Right Nothing; Just a -> f a >>= \b -> Right (Just b) }
b'HsPrelude'HsPt'cmaybe d f m = maybe d f m
b'HsPrelude'HsPt'ceither f g m = either f g m
b'HsPrelude'HsPt'errorq msg = Left msg
b'HsPrelude'HsPt'undefq = Left "Prelude.undefined"
b'HsPrelude'HsNum'div :: Integral a => a -> a -> Either String a
b'HsPrelude'HsNum'div a b = if b == 0 then Left "divide by zero" else Right (a `div` b)
b'HsPrelude'HsNum'sub :: (Ord a, Num a) => a -> a -> Either String a
b'HsPrelude'HsNum'sub a b = if a < b then Left "arithmetic underflow" else Right (a - b)
b'HsPrelude'HsNum'mod :: Integral a => a -> a -> Either String a
b'HsPrelude'HsNum'mod a b = if b == 0 then Left "divide by zero" else Right (a `mod` b)
b'HsPrelude'HsNum'idiv :: Integral a => a -> a -> Either String a
b'HsPrelude'HsNum'idiv a b = if b == 0 then Left "divide by zero" else Right (a `div` b)
b'HsPrelude'HsNum'imod :: Integral a => a -> a -> Either String a
b'HsPrelude'HsNum'imod a b = if b == 0 then Left "divide by zero" else Right (a `mod` b)
b'HsPrelude'HsNum'iquot :: Integral a => a -> a -> Either String a
b'HsPrelude'HsNum'iquot a b = if b == 0 then Left "divide by zero" else Right (a `quot` b)
b'HsPrelude'HsNum'irem :: Integral a => a -> a -> Either String a
b'HsPrelude'HsNum'irem a b = if b == 0 then Left "divide by zero" else Right (a `rem` b)
b'HsPrelude'HsNum'rdiv :: Rational -> Rational -> Either String Rational
b'HsPrelude'HsNum'rdiv a b = if b == 0 then Left "Ratio has zero denominator" else Right (a / b)

-- mapM and its kin at Maybe and at Either (HsPrelude.HsList.maybe.NAME,
-- HsPrelude.HsList.either.NAME)
b'HsPrelude'HsList'maybe'mapm :: (a -> Maybe b) -> [a] -> Maybe [b]
b'HsPrelude'HsList'maybe'mapm f xs = mapM f xs
b'HsPrelude'HsList'maybe'mapm_ :: (a -> Maybe b) -> [a] -> Maybe ()
b'HsPrelude'HsList'maybe'mapm_ f xs = mapM_ f xs
b'HsPrelude'HsList'maybe'seq :: [Maybe a] -> Maybe [a]
b'HsPrelude'HsList'maybe'seq xs = sequence xs
b'HsPrelude'HsList'maybe'cons :: Maybe a -> Maybe [a] -> Maybe [a]
b'HsPrelude'HsList'maybe'cons r rest = (:) <$> r <*> rest
b'HsPrelude'HsList'maybe'then :: Maybe a -> Maybe b -> Maybe b
b'HsPrelude'HsList'maybe'then r rest = r >> rest
b'HsPrelude'HsList'maybe'filterm p xs = case xs of { [] -> Just []; (x : t) -> p x >>= \k -> (if k then (x :) else id) <$> b'HsPrelude'HsList'maybe'filterm p t }
b'HsPrelude'HsList'maybe'foldm :: (b -> a -> Maybe b) -> [a] -> b -> Maybe b
b'HsPrelude'HsList'maybe'foldm f xs z = foldl (\acc h -> acc >>= \a -> f a h) (Just z) xs
b'HsPrelude'HsList'maybe'zipwithm_ f xs ys = sequence_ (zipWith f xs ys)
b'HsPrelude'HsList'either'mapm :: (a -> Either e b) -> [a] -> Either e [b]
b'HsPrelude'HsList'either'mapm f xs = mapM f xs
b'HsPrelude'HsList'either'mapm_ :: (a -> Either e b) -> [a] -> Either e ()
b'HsPrelude'HsList'either'mapm_ f xs = mapM_ f xs
b'HsPrelude'HsList'either'seq :: [Either e a] -> Either e [a]
b'HsPrelude'HsList'either'seq xs = sequence xs
b'HsPrelude'HsList'either'cons :: Either e a -> Either e [a] -> Either e [a]
b'HsPrelude'HsList'either'cons r rest = (:) <$> r <*> rest
b'HsPrelude'HsList'either'then :: Either e a -> Either e b -> Either e b
b'HsPrelude'HsList'either'then r rest = r >> rest
b'HsPrelude'HsList'either'filterm p xs = case xs of { [] -> Right []; (x : t) -> p x >>= \k -> (if k then (x :) else id) <$> b'HsPrelude'HsList'either'filterm p t }
b'HsPrelude'HsList'either'foldm :: (b -> a -> Either e b) -> [a] -> b -> Either e b
b'HsPrelude'HsList'either'foldm f xs z = foldl (\acc h -> acc >>= \a -> f a h) (Right z) xs
b'HsPrelude'HsList'either'zipwithm_ f xs ys = sequence_ (zipWith f xs ys)
b'HsPrelude'HsList'comparing cmp f x y = cmp (f x) (f y)

-- the prelude's comparisons (HsPrelude.HsCmp.NAME) and the module's
-- equalities (hs.eq.NAME), each a given element's
b'HsPrelude'HsCmp'bool a b = compare a (b :: Bool)
b'HsPrelude'HsCmp'char a b = compare a (b :: Char)
b'HsPrelude'HsCmp'unit a b = compare a (b :: ())
b'HsPrelude'HsCmp'list cmp xs ys = case (xs, ys) of
  ([], []) -> EQ
  ([], _) -> LT
  (_, []) -> GT
  (x : xt, y : yt) -> case cmp x y of { EQ -> b'HsPrelude'HsCmp'list cmp xt yt; o -> o }
b'HsPrelude'HsCmp'maybe cmp a b = case (a, b) of
  (Nothing, Nothing) -> EQ
  (Nothing, _) -> LT
  (_, Nothing) -> GT
  (Just x, Just y) -> cmp x y
b'HsPrelude'HsCmp'pair ca cb (a, b) (c, d) = case ca a c of { EQ -> cb b d; o -> o }
b'HsPrelude'HsCmp'on c lt eq gt = case c of { LT -> lt (); EQ -> eq (); GT -> gt () }
b'HsPrelude'HsCmp'either ca cb a b = case (a, b) of
  (Left x, Left y) -> ca x y
  (Left _, Right _) -> LT
  (Right _, Left _) -> GT
  (Right x, Right y) -> cb x y
b'HsPrelude'HsCmp'cmp a b = compare a (b :: Ordering)
b'HsPrelude'HsCmp'map ck cv a b = case (a, b) of
  (B'HsPrelude'HsMap'Tip, B'HsPrelude'HsMap'Tip) -> EQ
  (B'HsPrelude'HsMap'Tip, _) -> LT
  (_, B'HsPrelude'HsMap'Tip) -> GT
  (B'HsPrelude'HsMap'Bin k v s, B'HsPrelude'HsMap'Bin l w t) -> case ck k l of { EQ -> case cv v w of { EQ -> b'HsPrelude'HsCmp'map ck cv s t; o -> o }; o -> o }
b'HsPrelude'HsCmp'set ck a b = case (a, b) of
  (B'HsPrelude'HsSet'Tip, B'HsPrelude'HsSet'Tip) -> EQ
  (B'HsPrelude'HsSet'Tip, _) -> LT
  (_, B'HsPrelude'HsSet'Tip) -> GT
  (B'HsPrelude'HsSet'Bin k s, B'HsPrelude'HsSet'Bin l t) -> case ck k l of { EQ -> b'HsPrelude'HsCmp'set ck s t; o -> o }
b'HsPrelude'HsCmp'max cmp a b = if cmp a b /= GT then b else a
b'HsPrelude'HsCmp'min cmp a b = if cmp a b /= GT then a else b
b'hs'eq'cmp a b = a == (b :: Ordering)
b'hs'eq'unit a b = a == (b :: ())
b'hs'eq'either ea eb a b = case (a, b) of
  (Left x, Left y) -> ea x y
  (Right x, Right y) -> eb x y
  _ -> False
b'hs'maybe'alt x y = case x of { Nothing -> y (); _ -> x }

-- Data.Char's predicates (HsPrelude.HsChar.NAME: cata's tables are GHC's)
b'HsPrelude'HsChar'isAlpha = DC.isAlpha
b'HsPrelude'HsChar'isAlphaNum = DC.isAlphaNum
b'HsPrelude'HsChar'isDigit = DC.isDigit
b'HsPrelude'HsChar'isLower = DC.isLower
b'HsPrelude'HsChar'isUpper = DC.isUpper
b'HsPrelude'HsChar'isSpace = DC.isSpace
b'HsPrelude'HsChar'toUpper = DC.toUpper
b'HsPrelude'HsChar'toLower = DC.toLower

-- the prelude's recursion-scheme types (HsPrelude.Fix, .Cofree, .CofreeF
-- and its twin .CofreeF.fn), a type function F as Haskell's f
newtype B'HsPrelude'Fix f = B'HsPrelude'Fix'Fix (f (B'HsPrelude'Fix f))
data B'HsPrelude'Cofree f a = B'HsPrelude'Cofree'Cofree a (f (B'HsPrelude'Cofree f a))
data B'HsPrelude'CofreeF f a b = B'HsPrelude'CofreeF'CofreeF a (f b)
data B'HsPrelude'CofreeF'fn f a b = B'HsPrelude'CofreeF'fn'CofreeF a (f b)
b'HsPrelude'Fix'unFix (B'HsPrelude'Fix'Fix y) = y
b'HsPrelude'Cofree'project (B'HsPrelude'Cofree'Cofree h t) = B'HsPrelude'CofreeF'CofreeF h t
b'HsPrelude'Cofree'embed (B'HsPrelude'CofreeF'CofreeF h t) = B'HsPrelude'Cofree'Cofree h t

-- The round trip's iso at h's type.  G(F(t)) is t again up to an iso, not
-- equal: cata's Bend has pairs, not triples (h's (a, b, c) is G's (a, (b,
-- c))), and a partial h answers Either (b'unfail).  B'G t is G(F(t)) for a
-- Haskell type t (its numbers t itself: G's arithmetic is any Num's), and
-- b'up :: B'G t -> t is the iso, defined by t's structure: lists, Maybe,
-- Either, tuples and functions (b'down the other way, at a function's
-- argument); any other type, a module's own or a base one, is its own
-- image.  G writes each def GHC knows as h's name = b'up (G's def), and
-- the laws' script, whose every call names h's type, picks the iso.
type family B'G h where
  B'G [a] = [B'G a]
  B'G (Maybe a) = Maybe (B'G a)
  B'G (Either a b) = Either (B'G a) (B'G b)
  B'G (a, b) = (B'G a, B'G b)
  B'G (a, b, c) = (B'G a, (B'G b, B'G c))
  B'G (a, b, c, d) = (B'G a, (B'G b, (B'G c, B'G d)))
  B'G (a, b, c, d, e) = (B'G a, (B'G b, (B'G c, (B'G d, B'G e))))
  B'G (a -> b) = B'G a -> B'G b
  -- a type applied to 1 to 4 types (a module's own D a .., as G declares
  -- it): D at its arguments' images.  G writes D's B'Up (b'map'D at b'up
  -- and b'down, Back.bend's bk.mp) where it can follow D's fields; where it
  -- cannot, D's B'Up is the one below, so only at arguments that are their
  -- own images (an argument G reshapes, a triple, has no B'Up there)
  B'G (d a b c e) = d (B'G a) (B'G b) (B'G c) (B'G e)
  B'G (d a b c) = d (B'G a) (B'G b) (B'G c)
  B'G (d a b) = d (B'G a) (B'G b)
  B'G (d a) = d (B'G a)
  B'G a = a

class B'Up h where
  b'up :: B'G h -> h
  b'down :: h -> B'G h

instance B'Up a => B'Up [a] where
  b'up = map b'up
  b'down = map b'down
instance B'Up a => B'Up (Maybe a) where
  b'up = fmap b'up
  b'down = fmap b'down
instance (B'Up a, B'Up b) => B'Up (Either a b) where
  b'up = either (Left . b'up) (Right . b'up)
  b'down = either (Left . b'down) (Right . b'down)
instance (B'Up a, B'Up b) => B'Up (a, b) where
  b'up (a, b) = (b'up a, b'up b)
  b'down (a, b) = (b'down a, b'down b)
instance (B'Up a, B'Up b, B'Up c) => B'Up (a, b, c) where
  b'up (a, (b, c)) = (b'up a, b'up b, b'up c)
  b'down (a, b, c) = (b'down a, (b'down b, b'down c))
instance (B'Up a, B'Up b, B'Up c, B'Up d) => B'Up (a, b, c, d) where
  b'up (a, (b, (c, d))) = (b'up a, b'up b, b'up c, b'up d)
  b'down (a, b, c, d) = (b'down a, (b'down b, (b'down c, b'down d)))
instance (B'Up a, B'Up b, B'Up c, B'Up d, B'Up e) => B'Up (a, b, c, d, e) where
  b'up (a, (b, (c, (d, e)))) = (b'up a, b'up b, b'up c, b'up d, b'up e)
  b'down (a, b, c, d, e) = (b'down a, (b'down b, (b'down c, (b'down d, b'down e))))
instance (B'Up a, B'Up b) => B'Up (a -> b) where
  b'up f = b'up . f . b'down
  b'down f = b'down . f . b'up
instance {-# OVERLAPPABLE #-} (B'G a ~ a) => B'Up a where
  b'up = id
  b'down = id

-- the maps G's b'map'D (a module's own D with parameters, Back.bend's
-- bk.mp) is made of: a field without D's parameters (b'mid), a list's,
-- a Maybe's, an Either's, a pair's, and a function's (its argument the
-- other way)
b'mid :: a -> a
b'mid x = x
b'mlist :: (a -> b) -> [a] -> [b]
b'mlist = map
b'mmaybe :: (a -> b) -> Maybe a -> Maybe b
b'mmaybe = fmap
b'meither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
b'meither f g = either (Left . f) (Right . g)
b'mpair :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
b'mpair f g (a, b) = (f a, g b)
b'mfun :: (c -> a) -> (b -> d) -> (a -> b) -> c -> d
b'mfun g f h = f . h . g

-- a partial def's answer as h's: Inl{m} is h's error m again (the script's
-- LawEw answers an ErrorCall m as Inl m, as it does h's)
b'unfail :: Either String a -> a
b'unfail = either errorWithoutStackTrace id

-- G's converters between Bend's shape of a data field's type and h's (a
-- module's constructor with such a field is reached through a pattern
-- synonym that applies them): a list's, a Maybe's, an Either's and a
-- function's, of their parts' (a tuple's is a lambda G writes)
b'id :: a -> a
b'id x = x
b'cvL :: (a -> b) -> [a] -> [b]
b'cvL f = map f
b'cvM :: (a -> b) -> Maybe a -> Maybe b
b'cvM f = fmap f
b'cvE :: (a -> c) -> (b -> d) -> Either a b -> Either c d
b'cvE f g = either (Left . f) (Right . g)
b'cvF :: (c -> a) -> (b -> d) -> (a -> b) -> c -> d
b'cvF dn up h = up . h . dn

-- HsPrelude's Map and Set (Fold.bend's prelude: Data.Map's and Data.Set's
-- operations on a list kept sorted by the compare a call is given, one
-- constructor per key), as the prelude defines each: same answers, same
-- shapes
data B'HsPrelude'HsMap k v = B'HsPrelude'HsMap'Tip | B'HsPrelude'HsMap'Bin k v (B'HsPrelude'HsMap k v)
data B'HsPrelude'HsSet k = B'HsPrelude'HsSet'Tip | B'HsPrelude'HsSet'Bin k (B'HsPrelude'HsSet k)

b'HsPrelude'HsMap'insert cmp k v m = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Bin k v B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of
    LT -> B'HsPrelude'HsMap'Bin k v (B'HsPrelude'HsMap'Bin k2 v2 t)
    EQ -> B'HsPrelude'HsMap'Bin k v t
    GT -> B'HsPrelude'HsMap'Bin k2 v2 (b'HsPrelude'HsMap'insert cmp k v t)
b'HsPrelude'HsMap'insertWith cmp f k v m = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Bin k v B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of
    LT -> B'HsPrelude'HsMap'Bin k v (B'HsPrelude'HsMap'Bin k2 v2 t)
    EQ -> B'HsPrelude'HsMap'Bin k (f v v2) t
    GT -> B'HsPrelude'HsMap'Bin k2 v2 (b'HsPrelude'HsMap'insertWith cmp f k v t)
b'HsPrelude'HsMap'lookup cmp k m = case m of
  B'HsPrelude'HsMap'Tip -> Nothing
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of { LT -> Nothing; EQ -> Just v2; GT -> b'HsPrelude'HsMap'lookup cmp k t }
b'HsPrelude'HsMap'member cmp k m = case m of
  B'HsPrelude'HsMap'Tip -> False
  B'HsPrelude'HsMap'Bin k2 _ t -> case cmp k k2 of { LT -> False; EQ -> True; GT -> b'HsPrelude'HsMap'member cmp k t }
b'HsPrelude'HsMap'notMember cmp k m = not (b'HsPrelude'HsMap'member cmp k m)
b'HsPrelude'HsMap'findWithDefault cmp d k m = case m of
  B'HsPrelude'HsMap'Tip -> d
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of { LT -> d; EQ -> v2; GT -> b'HsPrelude'HsMap'findWithDefault cmp d k t }
b'HsPrelude'HsMap'delete cmp k m = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of { LT -> B'HsPrelude'HsMap'Bin k2 v2 t; EQ -> t; GT -> B'HsPrelude'HsMap'Bin k2 v2 (b'HsPrelude'HsMap'delete cmp k t) }
b'HsPrelude'HsMap'adjust cmp f k m = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of { LT -> B'HsPrelude'HsMap'Bin k2 v2 t; EQ -> B'HsPrelude'HsMap'Bin k2 (f v2) t; GT -> B'HsPrelude'HsMap'Bin k2 v2 (b'HsPrelude'HsMap'adjust cmp f k t) }
b'HsPrelude'HsMap'toList m = case m of { B'HsPrelude'HsMap'Tip -> []; B'HsPrelude'HsMap'Bin k v t -> (k, v) : b'HsPrelude'HsMap'toList t }
b'HsPrelude'HsMap'fromList'go cmp xs acc = case xs of { [] -> acc; (k, v) : t -> b'HsPrelude'HsMap'fromList'go cmp t (b'HsPrelude'HsMap'insert cmp k v acc) }
b'HsPrelude'HsMap'fromList cmp xs = b'HsPrelude'HsMap'fromList'go cmp xs B'HsPrelude'HsMap'Tip
b'HsPrelude'HsMap'fromListWith'go cmp f xs acc = case xs of { [] -> acc; (k, v) : t -> b'HsPrelude'HsMap'fromListWith'go cmp f t (b'HsPrelude'HsMap'insertWith cmp f k v acc) }
b'HsPrelude'HsMap'fromListWith cmp f xs = b'HsPrelude'HsMap'fromListWith'go cmp f xs B'HsPrelude'HsMap'Tip
b'HsPrelude'HsMap'elems m = map snd (b'HsPrelude'HsMap'toList m)
b'HsPrelude'HsMap'keys m = map fst (b'HsPrelude'HsMap'toList m)
b'HsPrelude'HsMap'keysSet m = case m of { B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsSet'Tip; B'HsPrelude'HsMap'Bin k _ t -> B'HsPrelude'HsSet'Bin k (b'HsPrelude'HsMap'keysSet t) }
b'HsPrelude'HsMap'size m = length (b'HsPrelude'HsMap'toList m)
b'HsPrelude'HsMap'null m = case m of { B'HsPrelude'HsMap'Tip -> True; _ -> False }
b'HsPrelude'HsMap'union cmp a b = case a of { B'HsPrelude'HsMap'Tip -> b; B'HsPrelude'HsMap'Bin k v t -> b'HsPrelude'HsMap'insert cmp k v (b'HsPrelude'HsMap'union cmp t b) }
b'HsPrelude'HsMap'unionWith cmp f a b = case a of { B'HsPrelude'HsMap'Tip -> b; B'HsPrelude'HsMap'Bin k v t -> b'HsPrelude'HsMap'insertWith cmp f k v (b'HsPrelude'HsMap'unionWith cmp f t b) }
b'HsPrelude'HsMap'difference cmp a b = case a of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k v t -> if b'HsPrelude'HsMap'member cmp k b then b'HsPrelude'HsMap'difference cmp t b else B'HsPrelude'HsMap'Bin k v (b'HsPrelude'HsMap'difference cmp t b)
b'HsPrelude'HsMap'map f m = case m of { B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip; B'HsPrelude'HsMap'Bin k v t -> B'HsPrelude'HsMap'Bin k (f v) (b'HsPrelude'HsMap'map f t) }
b'HsPrelude'HsMap'mapWithKey f m = case m of { B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip; B'HsPrelude'HsMap'Bin k v t -> B'HsPrelude'HsMap'Bin k (f k v) (b'HsPrelude'HsMap'mapWithKey f t) }
b'HsPrelude'HsMap'filter p m = case m of { B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip; B'HsPrelude'HsMap'Bin k v t -> if p v then B'HsPrelude'HsMap'Bin k v (b'HsPrelude'HsMap'filter p t) else b'HsPrelude'HsMap'filter p t }
b'HsPrelude'HsMap'filterWithKey p m = case m of { B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip; B'HsPrelude'HsMap'Bin k v t -> if p k v then B'HsPrelude'HsMap'Bin k v (b'HsPrelude'HsMap'filterWithKey p t) else b'HsPrelude'HsMap'filterWithKey p t }
b'HsPrelude'HsMap'foldr f z m = case m of { B'HsPrelude'HsMap'Tip -> z; B'HsPrelude'HsMap'Bin _ v t -> f v (b'HsPrelude'HsMap'foldr f z t) }
b'HsPrelude'HsMap'foldrWithKey f z m = case m of { B'HsPrelude'HsMap'Tip -> z; B'HsPrelude'HsMap'Bin k v t -> f k v (b'HsPrelude'HsMap'foldrWithKey f z t) }
b'HsPrelude'HsMap'eq eqk eqv a b = case (a, b) of
  (B'HsPrelude'HsMap'Tip, B'HsPrelude'HsMap'Tip) -> True
  (B'HsPrelude'HsMap'Bin k1 v1 t1, B'HsPrelude'HsMap'Bin k2 v2 t2) -> eqk k1 k2 && eqv v1 v2 && b'HsPrelude'HsMap'eq eqk eqv t1 t2
  _ -> False
b'HsPrelude'HsMap'empty = B'HsPrelude'HsMap'Tip
b'HsPrelude'HsMap'singleton k v = B'HsPrelude'HsMap'Bin k v B'HsPrelude'HsMap'Tip

b'HsPrelude'HsSet'insert cmp k s = case s of
  B'HsPrelude'HsSet'Tip -> B'HsPrelude'HsSet'Bin k B'HsPrelude'HsSet'Tip
  B'HsPrelude'HsSet'Bin k2 t -> case cmp k k2 of { LT -> B'HsPrelude'HsSet'Bin k (B'HsPrelude'HsSet'Bin k2 t); EQ -> B'HsPrelude'HsSet'Bin k2 t; GT -> B'HsPrelude'HsSet'Bin k2 (b'HsPrelude'HsSet'insert cmp k t) }
b'HsPrelude'HsSet'member cmp k s = case s of
  B'HsPrelude'HsSet'Tip -> False
  B'HsPrelude'HsSet'Bin k2 t -> case cmp k k2 of { LT -> False; EQ -> True; GT -> b'HsPrelude'HsSet'member cmp k t }
b'HsPrelude'HsSet'notMember cmp k s = not (b'HsPrelude'HsSet'member cmp k s)
b'HsPrelude'HsSet'delete cmp k s = case s of
  B'HsPrelude'HsSet'Tip -> B'HsPrelude'HsSet'Tip
  B'HsPrelude'HsSet'Bin k2 t -> case cmp k k2 of { LT -> B'HsPrelude'HsSet'Bin k2 t; EQ -> t; GT -> B'HsPrelude'HsSet'Bin k2 (b'HsPrelude'HsSet'delete cmp k t) }
b'HsPrelude'HsSet'toList s = case s of { B'HsPrelude'HsSet'Tip -> []; B'HsPrelude'HsSet'Bin k t -> k : b'HsPrelude'HsSet'toList t }
b'HsPrelude'HsSet'fromList'go cmp xs acc = case xs of { [] -> acc; k : t -> b'HsPrelude'HsSet'fromList'go cmp t (b'HsPrelude'HsSet'insert cmp k acc) }
b'HsPrelude'HsSet'fromList cmp xs = b'HsPrelude'HsSet'fromList'go cmp xs B'HsPrelude'HsSet'Tip
b'HsPrelude'HsSet'union cmp a b = case a of { B'HsPrelude'HsSet'Tip -> b; B'HsPrelude'HsSet'Bin k t -> b'HsPrelude'HsSet'insert cmp k (b'HsPrelude'HsSet'union cmp t b) }
b'HsPrelude'HsSet'unions cmp xs = case xs of { [] -> B'HsPrelude'HsSet'Tip; s : t -> b'HsPrelude'HsSet'union cmp s (b'HsPrelude'HsSet'unions cmp t) }
b'HsPrelude'HsSet'difference cmp a b = case a of
  B'HsPrelude'HsSet'Tip -> B'HsPrelude'HsSet'Tip
  B'HsPrelude'HsSet'Bin k t -> if b'HsPrelude'HsSet'member cmp k b then b'HsPrelude'HsSet'difference cmp t b else B'HsPrelude'HsSet'Bin k (b'HsPrelude'HsSet'difference cmp t b)
b'HsPrelude'HsSet'filter p s = case s of { B'HsPrelude'HsSet'Tip -> B'HsPrelude'HsSet'Tip; B'HsPrelude'HsSet'Bin k t -> if p k then B'HsPrelude'HsSet'Bin k (b'HsPrelude'HsSet'filter p t) else b'HsPrelude'HsSet'filter p t }
b'HsPrelude'HsSet'map'go cmp f s acc = case s of { B'HsPrelude'HsSet'Tip -> acc; B'HsPrelude'HsSet'Bin k t -> b'HsPrelude'HsSet'map'go cmp f t (b'HsPrelude'HsSet'insert cmp (f k) acc) }
b'HsPrelude'HsSet'map cmp f s = b'HsPrelude'HsSet'map'go cmp f s B'HsPrelude'HsSet'Tip
b'HsPrelude'HsSet'size s = length (b'HsPrelude'HsSet'toList s)
b'HsPrelude'HsSet'null s = case s of { B'HsPrelude'HsSet'Tip -> True; _ -> False }
b'HsPrelude'HsSet'eq eqk a b = case (a, b) of
  (B'HsPrelude'HsSet'Tip, B'HsPrelude'HsSet'Tip) -> True
  (B'HsPrelude'HsSet'Bin k1 t1, B'HsPrelude'HsSet'Bin k2 t2) -> eqk k1 k2 && b'HsPrelude'HsSet'eq eqk t1 t2
  _ -> False
b'HsPrelude'HsSet'empty = B'HsPrelude'HsSet'Tip
b'HsPrelude'HsSet'singleton k = B'HsPrelude'HsSet'Bin k B'HsPrelude'HsSet'Tip

-- HsPrelude's digest (crypton's Digest SHA256: its 32 bytes, each an Int
-- below 256): SHA-256 (FIPS 180-4) of a list of bytes, its hex text, its
-- order (the bytes', lexicographically), as the prelude's HsSha does it
data B'HsPrelude'HsDigest = B'HsPrelude'HsDigest'D [Int]

b'sha'k :: [Word32]
b'sha'k = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

b'sha'h0 :: [Word32]
b'sha'h0 = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

b'sha'pad :: [Int] -> [Word32]
b'sha'pad m = words4 (map fromIntegral m ++ [0x80] ++ replicate z 0 ++ [fromIntegral (bits `shiftR` (8 * i)) .&. 255 | i <- [7, 6 .. 0]])
  where
    n = length m
    z = (55 - n) `mod` 64
    bits = fromIntegral n * 8 :: Word64
    words4 (a : b : c : d : r) = (a `shiftL` 24 .|. b `shiftL` 16 .|. c `shiftL` 8 .|. d) : words4 r
    words4 _ = []

b'sha'block :: [Word32] -> [Word32] -> [Word32]
b'sha'block hs ws16 = zipWith (+) hs (go 0 hs)
  where
    w = take 64 (ws16 ++ [ s1 (w !! (i - 2)) + w !! (i - 7) + s0 (w !! (i - 15)) + w !! (i - 16) | i <- [16 .. 63] ])
    s0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3
    s1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10
    go 64 v = v
    go i [a, b, c, d, e, f, g, h] =
      let t1 = h + (rotateR e 6 `xor` rotateR e 11 `xor` rotateR e 25) + ((e .&. f) `xor` (complement e .&. g)) + b'sha'k !! i + w !! i
          t2 = (rotateR a 2 `xor` rotateR a 13 `xor` rotateR a 22) + ((a .&. b) `xor` (a .&. c) `xor` (b .&. c))
      in go (i + 1) [t1 + t2, a, b, c, d + t1, e, f, g]
    go _ v = v

b'HsPrelude'HsDigest'hash :: [Int] -> B'HsPrelude'HsDigest
b'HsPrelude'HsDigest'hash m = B'HsPrelude'HsDigest'D (concatMap bytes (foldl b'sha'block b'sha'h0 (chunks (b'sha'pad m))))
  where
    chunks [] = []
    chunks xs = take 16 xs : chunks (drop 16 xs)
    bytes x = [fromIntegral (x `shiftR` s .&. 255) | s <- [24, 16, 8, 0]]

b'HsPrelude'HsDigest'bytes (B'HsPrelude'HsDigest'D bs) = bs
b'HsPrelude'HsDigest'fromBytes bs = if length bs == 32 then Just (B'HsPrelude'HsDigest'D bs) else Nothing
b'HsPrelude'HsDigest'hexs d = concatMap (\b -> [hexd (b `div` 16), hexd (b `mod` 16)]) (b'HsPrelude'HsDigest'bytes d)
  where hexd n = toEnum (if n < 10 then n + 48 else n + 87) :: Char
b'HsPrelude'HsUtf8'encode s = concatMap (enc . fromEnum) (s :: String)
  where
    enc c | c < 0x80 = [c]
          | c < 0x800 = [0xc0 + c `div` 64, 0x80 + c `mod` 64]
          | c < 0x10000 = [0xe0 + c `div` 4096, 0x80 + c `div` 64 `mod` 64, 0x80 + c `mod` 64]
          | otherwise = [0xf0 + c `div` 262144, 0x80 + c `div` 4096 `mod` 64, 0x80 + c `div` 64 `mod` 64, 0x80 + c `mod` 64 :: Int]
b'HsPrelude'HsDigest'cmp a b = compare (b'HsPrelude'HsDigest'bytes a) (b'HsPrelude'HsDigest'bytes b)
b'HsPrelude'HsDigest'is_eq a b = b'HsPrelude'HsDigest'cmp a b == EQ

-- the prelude's Map and Set functions after the first ones (Prelude.bend)
b'HsPrelude'HsMap'insertWithKey cmp f k v m = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Bin k v B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of
    LT -> B'HsPrelude'HsMap'Bin k v (B'HsPrelude'HsMap'Bin k2 v2 t)
    EQ -> B'HsPrelude'HsMap'Bin k (f k v v2) t
    GT -> B'HsPrelude'HsMap'Bin k2 v2 (b'HsPrelude'HsMap'insertWithKey cmp f k v t)
b'HsPrelude'HsMap'unionWithKey cmp f a b = case a of { B'HsPrelude'HsMap'Tip -> b; B'HsPrelude'HsMap'Bin k v t -> b'HsPrelude'HsMap'insertWithKey cmp f k v (b'HsPrelude'HsMap'unionWithKey cmp f t b) }
b'HsPrelude'HsMap'unionsWith'go cmp f ms acc = case ms of { [] -> acc; m : t -> b'HsPrelude'HsMap'unionsWith'go cmp f t (b'HsPrelude'HsMap'unionWith cmp f acc m) }
b'HsPrelude'HsMap'unionsWith cmp f ms = case ms of { [] -> B'HsPrelude'HsMap'Tip; m : t -> b'HsPrelude'HsMap'unionsWith'go cmp f t m }
b'HsPrelude'HsMap'intersectionWith cmp f a b = case a of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k v t -> let r = b'HsPrelude'HsMap'intersectionWith cmp f t b in case b'HsPrelude'HsMap'lookup cmp k b of { Nothing -> r; Just x -> B'HsPrelude'HsMap'Bin k (f v x) r }
b'HsPrelude'HsMap'restrictKeys cmp m s = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k v t -> if b'HsPrelude'HsSet'member cmp k s then B'HsPrelude'HsMap'Bin k v (b'HsPrelude'HsMap'restrictKeys cmp t s) else b'HsPrelude'HsMap'restrictKeys cmp t s
b'HsPrelude'HsMap'withoutKeys cmp m s = case m of
  B'HsPrelude'HsMap'Tip -> B'HsPrelude'HsMap'Tip
  B'HsPrelude'HsMap'Bin k v t -> if b'HsPrelude'HsSet'member cmp k s then b'HsPrelude'HsMap'withoutKeys cmp t s else B'HsPrelude'HsMap'Bin k v (b'HsPrelude'HsMap'withoutKeys cmp t s)
b'HsPrelude'HsMap'fromSet f s = case s of { B'HsPrelude'HsSet'Tip -> B'HsPrelude'HsMap'Tip; B'HsPrelude'HsSet'Bin k t -> B'HsPrelude'HsMap'Bin k (f k) (b'HsPrelude'HsMap'fromSet f t) }
b'HsPrelude'HsMap'split cmp k m = case m of
  B'HsPrelude'HsMap'Tip -> (B'HsPrelude'HsMap'Tip, B'HsPrelude'HsMap'Tip)
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k2 k of
    LT -> let (a, b) = b'HsPrelude'HsMap'split cmp k t in (B'HsPrelude'HsMap'Bin k2 v2 a, b)
    EQ -> (B'HsPrelude'HsMap'Tip, t)
    GT -> (B'HsPrelude'HsMap'Tip, B'HsPrelude'HsMap'Bin k2 v2 t)
b'HsPrelude'HsSet'intersection cmp a b = case a of
  B'HsPrelude'HsSet'Tip -> B'HsPrelude'HsSet'Tip
  B'HsPrelude'HsSet'Bin k t -> if b'HsPrelude'HsSet'member cmp k b then B'HsPrelude'HsSet'Bin k (b'HsPrelude'HsSet'intersection cmp t b) else b'HsPrelude'HsSet'intersection cmp t b
b'HsPrelude'HsMap'isize m = b'HsPrelude'HsMap'size m
b'HsPrelude'HsSet'isize s = b'HsPrelude'HsSet'size s
-- Map.! as a failure value (the prelude's partial functions answer Either)
b'HsPrelude'HsMap'at cmp m k = case m of
  B'HsPrelude'HsMap'Tip -> Left "Map.!: given key is not an element in the map"
  B'HsPrelude'HsMap'Bin k2 v2 t -> case cmp k k2 of { LT -> Left "Map.!: given key is not an element in the map"; EQ -> Right v2; GT -> b'HsPrelude'HsMap'at cmp t k }

-- HsPrelude's show at Int, a list and Maybe (HsShow.int, .list, .maybe)
b'HsPrelude'HsShow'int d n r = if n >= 0 then show n ++ r else b'HsPrelude'HsShow'paren (d > 6) (\s -> '-' : show (negate n) ++ s) r
b'HsPrelude'HsShow'list'rest sh xs r = case xs of { [] -> ']' : r; x : t -> ',' : sh x (b'HsPrelude'HsShow'list'rest sh t r) }
b'HsPrelude'HsShow'list sh xs r = case xs of { [] -> '[' : ']' : r; x : t -> '[' : sh x (b'HsPrelude'HsShow'list'rest sh t r) }
b'HsPrelude'HsShow'maybe sh d m r = case m of { Nothing -> "Nothing" ++ r; Just x -> b'HsPrelude'HsShow'paren (d >= 11) (\s -> "Just " ++ sh 11 x s) r }

-- State s a as each module's prelude has it (hs.state.*: s -> (a, s))
b'hs'state'bind m f = \s -> let (a, s') = m s in f a s'
b'hs'state'bind'go p f = let (a, s) = p in f a s
b'hs'state'map'go f p = let (a, s) = p in (f a, s)
b'hs'state'pure a = \s -> (a, s)
b'hs'state'map f m = \s -> let (a, s') = m s in (f a, s')
b'hs'state'ap mf m = \s -> let (f, s') = mf s in b'hs'state'map f m s'
b'hs'state'dup s = (s, s)
b'hs'state'get = \s -> (s, s)
b'hs'state'put s = \_ -> ((), s)
b'hs'state'modify f = \s -> ((), f s)
b'hs'state'gets f = \s -> (f s, s)
b'hs'state'fst (a, _) = a
b'hs'state'snd (_, s) = s
b'hs'state're p = p
b'hs'state'eval m s = fst (m s)
b'hs'state'exec m s = snd (m s)
b'hs'state'run m s = m s
b'hs'state'mapm_ f xs = case xs of { [] -> b'hs'state'pure (); h : t -> b'hs'state'bind (f h) (\_ -> b'hs'state'mapm_ f t) }
b'hs'state'mapm f xs = case xs of { [] -> b'hs'state'pure []; h : t -> b'hs'state'bind (f h) (\b -> b'hs'state'map (b :) (b'hs'state'mapm f t)) }
b'hs'state'foldm f xs z = case xs of { [] -> b'hs'state'pure z; h : t -> b'hs'state'bind (f z h) (\y -> b'hs'state'foldm f t y) }
b'hs'state'seq xs = case xs of { [] -> b'hs'state'pure []; h : t -> b'hs'state'bind h (\b -> b'hs'state'map (b :) (b'hs'state'seq t)) }
b'hs'state'keep k x ys = if k then x : ys else ys
b'hs'state'filterm p xs = case xs of { [] -> b'hs'state'pure []; h : t -> b'hs'state'bind (p h) (\k -> b'hs'state'map (\ys -> b'hs'state'keep k h ys) (b'hs'state'filterm p t)) }
b'hs'state'zipwithm_ f xs ys = case (xs, ys) of { (x : xt, y : yt) -> b'hs'state'bind (f x y) (\_ -> b'hs'state'zipwithm_ f xt yt); _ -> b'hs'state'pure () }

-- HsPrelude's show at a pair, a Map, a Set; first at a pair
b'HsPrelude'HsShow'pair sa sb (a, b) r = '(' : sa 0 a (',' : sb 0 b (')' : r))
b'HsPrelude'HsShow'listP sp _ xs r = b'HsPrelude'HsShow'list (\y t -> sp 0 y t) xs r
b'HsPrelude'HsShow'pairP sa sb _ p r = b'HsPrelude'HsShow'pair sa sb p r
b'HsPrelude'HsShow'map sk sv d m r = b'HsPrelude'HsShow'paren (d >= 11) (\s -> "fromList " ++ b'HsPrelude'HsShow'list (\y t -> b'HsPrelude'HsShow'pair sk sv y t) (b'HsPrelude'HsMap'toList m) s) r
b'HsPrelude'HsShow'set sk d m r = b'HsPrelude'HsShow'paren (d >= 11) (\s -> "fromList " ++ b'HsPrelude'HsShow'list (\y t -> sk 0 y t) (b'HsPrelude'HsSet'toList m) s) r
b'HsPrelude'HsList'first'pair f (a, c) = (f a, c)

-- Reader r a, ReaderT r (Either e) a and WriterT w (Either e) a as each
-- module's prelude has them (hs.rd.*, hs.rde.*, hs.wre.*: the writer's
-- defs take w's mempty and <> first)
b'hs'rd'bind'go m f r = f (m r) r
b'hs'rd'bind m f = \r -> f (m r) r
b'hs'rd'pure a = \_ -> a
b'hs'rd'map f m = \r -> f (m r)
b'hs'rd'ask = \r -> r
b'hs'rd'local f m = \r -> m (f r)
b'hs'rd'asks f = \r -> f r
b'hs'rde'bind'go x f r = case x of { Left e -> Left e; Right a -> f a r }
b'hs'rde'bind'r m f r = b'hs'rde'bind'go (m r) f r
b'hs'rde'bind m f = \r -> b'hs'rde'bind'r m f r
b'hs'rde'pure a = \_ -> Right a
b'hs'rde'throw e = \_ -> Left e
b'hs'rde'lift x = \_ -> x
b'hs'rde'map'e f x = case x of { Left e -> Left e; Right a -> Right (f a) }
b'hs'rde'map f m = \r -> b'hs'rde'map'e f (m r)
b'hs'rde'ask = \r -> Right r
b'hs'rde'local f m = \r -> m (f r)
b'hs'rde'asks f = \r -> Right (f r)
-- (signatures: a def that does not run its app, the log's <>, still has it at
-- the log's type, or GHC finds that type ambiguous in what G writes)
b'hs'wr'pure :: w -> (w -> w -> w) -> a -> (a, w)
b'hs'wr'map :: w -> (w -> w -> w) -> (a -> b) -> (a, w) -> (b, w)
b'hs'wr'bind :: w -> (w -> w -> w) -> (a, w) -> (a -> (b, w)) -> (b, w)
b'hs'wre'pure :: w -> (w -> w -> w) -> a -> Either e (a, w)
b'hs'wre'map :: w -> (w -> w -> w) -> (a -> b) -> Either e (a, w) -> Either e (b, w)
b'hs'wre'bind :: w -> (w -> w -> w) -> Either e (a, w) -> (a -> Either e (b, w)) -> Either e (b, w)
b'hs'stp'pure :: w -> (w -> w -> w) -> a -> s -> (w, (a, s))
b'hs'stp'map :: w -> (w -> w -> w) -> (a -> b) -> (s -> (w, (a, s))) -> s -> (w, (b, s))
b'hs'stp'bind :: w -> (w -> w -> w) -> (s -> (w, (a, s))) -> (a -> s -> (w, (b, s))) -> s -> (w, (b, s))
b'hs'stp'get :: w -> (w -> w -> w) -> s -> (w, (s, s))
b'hs'stp'put :: w -> (w -> w -> w) -> s -> s -> (w, ((), s))
b'hs'stp'modify :: w -> (w -> w -> w) -> (s -> s) -> s -> (w, ((), s))
b'hs'stp'gets :: w -> (w -> w -> w) -> (s -> a) -> s -> (w, (a, s))
b'hs'wr'join app w y = case y of { (b, v) -> (b, app w v) }
b'hs'wr'bind mt app x f = case x of { (a, w) -> b'hs'wr'join app w (f a) }
b'hs'wr'pure mt app a = (a, mt)
b'hs'wr'map mt app f x = case x of { (a, w) -> (f a, w) }
b'hs'wre'join app w y = case y of { Left e -> Left e; Right (b, v) -> Right (b, app w v) }
b'hs'wre'bind mt app x f = case x of { Left e -> Left e; Right (a, w) -> b'hs'wre'join app w (f a) }
b'hs'wre'pure mt app a = Right (a, mt)
b'hs'wre'map mt app f x = case x of { Left e -> Left e; Right (a, w) -> Right (f a, w) }

-- ExceptT e (State s) a as each module's prelude has it (hs.exs.*:
-- s -> (Either e a, s), >>= stops at a Left and keeps the state)
b'hs'exs'bind m f = \s -> case m s of { (Left e, s') -> (Left e, s'); (Right a, s') -> f a s' }
b'hs'exs'bind'p p f = case p of { (Left e, s) -> (Left e, s); (Right a, s) -> f a s }
b'hs'exs'map'go f p = let (r, s') = p in (fmap f r, s')
b'hs'exs'pure a = \s -> (Right a, s)
b'hs'exs'throw e = \s -> (Left e, s)
b'hs'exs'map f m = \s -> let (r, s') = m s in (fmap f r, s')
b'hs'exs'dup s = (Right s, s)
b'hs'exs'get = \s -> (Right s, s)
b'hs'exs'put s = \_ -> (Right (), s)
b'hs'exs'modify f = \s -> (Right (), f s)
b'hs'exs'gets f = \s -> (Right (f s), s)
b'hs'exs'mapm_ f xs = case xs of { [] -> b'hs'exs'pure (); h : t -> b'hs'exs'bind (f h) (\_ -> b'hs'exs'mapm_ f t) }
b'hs'exs'mapm f xs = case xs of { [] -> b'hs'exs'pure []; h : t -> b'hs'exs'bind (f h) (\b -> b'hs'exs'map (b :) (b'hs'exs'mapm f t)) }
b'hs'exs'foldm f xs z = case xs of { [] -> b'hs'exs'pure z; h : t -> b'hs'exs'bind (f z h) (\y -> b'hs'exs'foldm f t y) }
b'hs'exs'seq xs = case xs of { [] -> b'hs'exs'pure []; h : t -> b'hs'exs'bind h (\b -> b'hs'exs'map (b :) (b'hs'exs'seq t)) }
b'hs'exs'keep k x ys = if k then x : ys else ys
b'hs'exs'filterm p xs = case xs of { [] -> b'hs'exs'pure []; h : t -> b'hs'exs'bind (p h) (\k -> b'hs'exs'map (\ys -> b'hs'exs'keep k h ys) (b'hs'exs'filterm p t)) }
b'hs'exs'zipwithm_ f xs ys = case (xs, ys) of { (x : xt, y : yt) -> b'hs'exs'bind (f x y) (\_ -> b'hs'exs'zipwithm_ f xt yt); _ -> b'hs'exs'pure () }

-- StateT s (Either e) a and StateT s ((,) w) a as each module's prelude
-- has them (hs.ste.*, hs.stp.*: s -> Either e (a, s), s -> (w, (a, s));
-- hs.stp's defs take w's mempty and <> first, as the fold writes them)
b'hs'ste'bind m f = \s -> case m s of { Left e -> Left e; Right (a, s') -> f a s' }
b'hs'ste'pure a = \s -> Right (a, s)
b'hs'ste'throw e = \_ -> Left e
b'hs'ste'map f m = \s -> case m s of { Left e -> Left e; Right (a, s') -> Right (f a, s') }
b'hs'ste'get = \s -> Right (s, s)
b'hs'ste'put s = \_ -> Right ((), s)
b'hs'ste'modify f = \s -> Right ((), f s)
b'hs'ste'gets f = \s -> Right (f s, s)
b'hs'ste'lift m = \s -> case m of { Left e -> Left e; Right a -> Right (a, s) }
b'hs'ste'eval m s = case m s of { Left e -> Left e; Right (a, _) -> Right a }
b'hs'ste'exec m s = case m s of { Left e -> Left e; Right (_, s') -> Right s' }
b'hs'ste'run m s = m s
b'hs'stp'bind mt app m f = \s -> case m s of { (w, (a, s')) -> case f a s' of { (v, r) -> (app w v, r) } }
b'hs'stp'pure mt app a = \s -> (mt, (a, s))
b'hs'stp'map mt app f m = \s -> case m s of { (w, (a, s')) -> (w, (f a, s')) }
b'hs'stp'get mt app = \s -> (mt, (s, s))
b'hs'stp'put mt app s = \_ -> (mt, ((), s))
b'hs'stp'modify mt app f = \s -> (mt, ((), f s))
b'hs'stp'gets mt app f = \s -> (mt, (f s, s))
b'hs'stp'lift m = \s -> case m of { (w, a) -> (w, (a, s)) }
b'hs'stp'eval m s = case m s of { (w, (a, _)) -> (w, a) }
b'hs'stp'exec m s = case m s of { (w, (_, s')) -> (w, s') }
b'hs'stp'run m s = m s

-- zipWith f [n ..] xs at an enumeration's successor, second at a pair,
-- show by showsPrec 0 (the prelude's HsList.zipWithFrom, .second.pair,
-- HsShow.via)
b'HsPrelude'HsList'zipWithFrom'go sc f xs n = case xs of { [] -> []; x : t -> f n x : b'HsPrelude'HsList'zipWithFrom'go sc f t (sc n) }
b'HsPrelude'HsList'zipWithFrom sc f n xs = b'HsPrelude'HsList'zipWithFrom'go sc f xs n
b'HsPrelude'HsList'zipFrom'go sc xs n = case xs of { [] -> []; x : t -> (n, x) : b'HsPrelude'HsList'zipFrom'go sc t (sc n) }
b'HsPrelude'HsList'zipFrom sc n xs = b'HsPrelude'HsList'zipFrom'go sc xs n
b'HsPrelude'HsList'zipR sc xs n = case xs of { [] -> []; x : t -> (x, n) : b'HsPrelude'HsList'zipR sc t (sc n) }
b'HsPrelude'HsList'zipWithR sc f xs n = case xs of { [] -> []; x : t -> f x n : b'HsPrelude'HsList'zipWithR sc f t (sc n) }
b'HsPrelude'HsList'splitAt n xs = splitAt n xs
b'HsPrelude'HsList'transpose xss = case dropWhile null xss of { [] -> []; yss -> [h | h : _ <- yss] : b'HsPrelude'HsList'transpose [t | _ : t <- yss] }
b'HsPrelude'HsList'dropWhileEnd p xs = foldr (\x r -> if p x && null r then [] else x : r) [] xs
b'HsPrelude'HsList'uncons xs = case xs of { [] -> Nothing; h : t -> Just (h, t) }
b'HsPrelude'HsList'scanl f q xs = scanl f q xs
b'HsPrelude'HsList'elemIndex eq x xs = case [i | (i, y) <- zip [0 ..] xs, eq x y] of { [] -> Nothing; i : _ -> Just i }
b'HsPrelude'HsList'second'pair f (a, b) = (a, f b)
b'HsPrelude'HsShow'via sp x = sp 0 x []

-- HsPrelude's Rational (prelude/HsRational.bend: Data.Ratio's Ratio Integer
-- in lowest terms, the denominator at least 1) as Haskell's own Rational;
-- each operation as the prelude defines it: a zero denominator (x / 0,
-- n % 0) answers 0 where GHC throws "Ratio has zero denominator"
type B'HsPrelude'HsRational = Rational
b'HsPrelude'HsRational'gcd'go fuel a b = if fuel == 0 || b == 0 then a else b'HsPrelude'HsRational'gcd'go (fuel - 1) b (a `mod` b)
b'HsPrelude'HsRational'gcd a b = gcd a b
b'HsPrelude'HsRational'zero = 0 :: Rational
b'HsPrelude'HsRational'mk n d = if d == 0 then 0 else toInteger n % toInteger d :: Rational
b'HsPrelude'HsRational'mk'at g n d = if g == 0 then 0 else b'HsPrelude'HsRational'mk n d
b'HsPrelude'HsRational'of n = fromIntegral n :: Rational
b'HsPrelude'HsRational'numerator r = fromInteger (numerator (r :: Rational))
b'HsPrelude'HsRational'denominator r = fromInteger (denominator (r :: Rational))
b'HsPrelude'HsRational'add a b = a + (b :: Rational)
b'HsPrelude'HsRational'negate a = negate (a :: Rational)
b'HsPrelude'HsRational'sub a b = a - (b :: Rational)
b'HsPrelude'HsRational'mul a b = a * (b :: Rational)
b'HsPrelude'HsRational'div a b = if b == 0 then 0 else a / (b :: Rational)
b'HsPrelude'HsRational'abs a = abs (a :: Rational)
b'HsPrelude'HsRational'signum a = signum (a :: Rational)
b'HsPrelude'HsRational'cmp a b = compare a (b :: Rational)
b'HsPrelude'HsRational'is_eq a b = a == (b :: Rational)
b'HsPrelude'HsRational'is_ne a b = a /= (b :: Rational)
b'HsPrelude'HsRational'is_lt a b = a < (b :: Rational)
b'HsPrelude'HsRational'is_le a b = a <= (b :: Rational)
b'HsPrelude'HsRational'is_gt a b = a > (b :: Rational)
b'HsPrelude'HsRational'is_ge a b = a >= (b :: Rational)
b'HsPrelude'HsRational'max a b = if a >= (b :: Rational) then a else b
b'HsPrelude'HsRational'min a b = if a <= (b :: Rational) then a else b
b'HsPrelude'HsRational'shows d x r = showsPrec d (x :: Rational) r
b'HsPrelude'HsRational'show x = show (x :: Rational)
b'HsPrelude'HsInt'ratio a b = if b == 0 then 0 else toInteger a % toInteger b :: Rational
b'HsPrelude'HsInt'lcm'at g a b = if g == 0 then 0 else (a `div` g) * b
-- the record HsRational{num, den}: a view of a Rational, and built as GHC's
-- n % d (G writes it for fuel's default, HsRational{Pos{0}, 1}, and other
-- literals)
b'ratv :: Rational -> (Int, Int)
b'ratv r = (fromInteger (numerator r), fromInteger (denominator r))
pattern B'HsPrelude'HsRational :: Int -> Int -> Rational
pattern B'HsPrelude'HsRational n d <- (b'ratv -> (n, d)) where B'HsPrelude'HsRational n d = b'HsPrelude'HsRational'mk n d
{-# COMPLETE B'HsPrelude'HsRational #-}

-- first, second and bimap at Either, bimap at a pair (the prelude's
-- HsList.first.either, .second.either, .bimap.either, .bimap.pair)
b'HsPrelude'HsList'first'either f e = case e of { Left a -> Left (f a); Right c -> Right c }
b'HsPrelude'HsList'second'either f e = case e of { Left a -> Left a; Right b -> Right (f b) }
b'HsPrelude'HsList'bimap'either f g e = case e of { Left a -> Left (f a); Right c -> Right (g c) }
b'HsPrelude'HsList'bimap'pair f g (a, c) = (f a, g c)
