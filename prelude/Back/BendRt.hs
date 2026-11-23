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
{-# LANGUAGE NoMonomorphismRestriction #-}
module BendRt
  ( module BendRt
  , Bool (..), Maybe (..), Either (..), Ordering (..), Int, Char, String
  , (.), ($)
  ) where

import Prelude
import qualified Data.Char as DC
import Data.List (sortBy, nubBy, isPrefixOf, isSuffixOf, isInfixOf, intercalate, intersperse, groupBy, insertBy, tails, inits, partition, stripPrefix)
import Data.Maybe (mapMaybe, catMaybes, isJust, isNothing, listToMaybe, maybeToList)
import Data.Either (lefts, rights, partitionEithers, isLeft, isRight, fromLeft, fromRight)

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

-- what G could not write
b'todo :: a
b'todo = error "bend2hs: a form G does not write"

-- a Nat pattern 1n+p
b'pred :: Integral a => a -> Maybe a
b'pred n = if n >= 1 then Just (n - 1) else Nothing

b'chr :: Int -> Char
b'chr = toEnum

-- cata's prelude: an if with thunks
b'Bool'if c t e = if c then t () else e ()

b'Bool'and a b = a && b
b'Bool'or a b = a || b
b'Bool'not = not
b'Bool'xor a b = a /= b
b'Bool'is_eq a b = a == (b :: Bool)
b'Bool'pick c a b = if c then a else b

b'Nat'add a b = a + b
b'Nat'sub a b = max 0 (a - b)
b'Nat'mul a b = a * b
b'Nat'div a b = if b == 0 then 0 else a `div` b
b'Nat'mod a b = if b == 0 then a else a `mod` b
b'Nat'pow a b = a ^ b
b'Nat'max a b = max a b
b'Nat'min a b = min a b
b'Nat'is_eq a b = a == b
b'Nat'is_ne a b = a /= b
b'Nat'is_lt a b = a < b
b'Nat'is_le a b = a <= b
b'Nat'is_gt a b = a > b
b'Nat'is_ge a b = a >= b
b'Nat'cmp a b = compare a b
b'Nat'show n = show n
b'Nat'succ n = n + 1
b'Nat'pred n = max 0 (n - 1)
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

b'List'append xs ys = xs ++ ys
b'List'length xs = length xs
b'List'reverse = reverse
b'List'concat = concat
b'List'map f xs = map f xs
b'List'filter f xs = filter f xs
b'List'any f xs = any f xs
b'List'all f xs = all f xs
b'List'take xs n = take n xs
b'List'drop xs n = drop n xs
b'List'replicate n x = replicate n x
b'List'contains eq xs x = any (eq x) xs
b'List'foldr f xs z = foldr f z xs
b'List'foldl f xs z = foldl f z xs
b'List'is_empty = null
b'List'head xs = listToMaybe xs
b'List'tail xs = drop 1 xs
b'List'last xs = if null xs then Nothing else Just (last xs)
b'List'zip xs ys = zip xs ys
b'List'sum xs = sum xs

b'Maybe'map f m = fmap f m
b'Maybe'bind m f = m >>= f
b'Maybe'default m d = maybe d id m

-- cata's module prelude (hs.*)
b'hs'map f xs = map f xs
b'hs'maybe d f m = maybe d f m
b'hs'either f g e = either f g e
b'hs'either'bind m f = m >>= f
b'hs'either'map f m = fmap f m
b'hs'eq'list eq xs ys = length xs == length ys && and (zipWith eq xs ys)
b'hs'eq'maybe eq a b = case (a, b) of
  (Nothing, Nothing) -> True
  (Just x, Just y) -> eq x y
  _ -> False
b'hs'eq'pair ea eb (a, b) (c, d) = ea a c && eb b d

-- HsPrelude's lists (HsPrelude.HsList.NAME)
b'HsPrelude'HsList'foldr f xs z = foldr f z xs
b'HsPrelude'HsList'foldl f xs z = foldl f z xs
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
b'HsPrelude'HsList'elem eq x xs = any (eq x) xs
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
