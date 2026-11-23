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
{-# LANGUAGE NoMonomorphismRestriction, PatternSynonyms, ViewPatterns #-}
module BendRt
  ( module BendRt
  , Bool (..), Maybe (..), Either (..), Ordering (..), Int, Char, String, Float, IO
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

-- a module Main's main, which no law runs
b'main :: IO ()
b'main = return ()

-- Base's U32 (an Int below 2^32: cata writes a U32 for a character's code
-- and for a fuel bound) and F32 (a Float)
b'U32'to_nat n = n :: Int
b'U32'from_nat n = n :: Int
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
b'F32'from_nat n = fromIntegral (n :: Int) :: Float

-- the prelude's Haskell Int (HsPrelude.HsInt): Pos n and Neg n as views of
-- an Int; each operation as the prelude defines it (quot, rem, div and mod
-- by 0 are the prelude's total answers: Nat.div n 0 is 0, Nat.mod n 0 n)
b'posv :: Int -> Maybe Int
b'posv k = if k >= 0 then Just k else Nothing
b'negv :: Int -> Maybe Int
b'negv k = if k < 0 then Just (negate k) else Nothing
pattern B'HsPrelude'HsInt'Pos :: Int -> Int
pattern B'HsPrelude'HsInt'Pos n <- (b'posv -> Just n) where B'HsPrelude'HsInt'Pos n = n
pattern B'HsPrelude'HsInt'Neg :: Int -> Int
pattern B'HsPrelude'HsInt'Neg n <- (b'negv -> Just n) where B'HsPrelude'HsInt'Neg n = negate n
{-# COMPLETE B'HsPrelude'HsInt'Pos, B'HsPrelude'HsInt'Neg #-}

b'HsPrelude'HsInt'of n = n :: Int
b'HsPrelude'HsInt'neg'of n = negate n :: Int
b'HsPrelude'HsInt'negate a = negate a :: Int
b'HsPrelude'HsInt'nsub a b = a - b :: Int
b'HsPrelude'HsInt'add a b = a + b :: Int
b'HsPrelude'HsInt'sub a b = a - b :: Int
b'HsPrelude'HsInt'mul a b = a * b :: Int
b'HsPrelude'HsInt'abs a = abs a :: Int
b'HsPrelude'HsInt'signum a = signum a :: Int
b'HsPrelude'HsInt'mag a = abs a :: Int
b'HsPrelude'HsInt'isneg a = a < (0 :: Int)
b'HsPrelude'HsInt'cmp a b = compare a (b :: Int)
b'HsPrelude'HsInt'is_eq a b = a == (b :: Int)
b'HsPrelude'HsInt'is_ne a b = a /= (b :: Int)
b'HsPrelude'HsInt'is_lt a b = a < (b :: Int)
b'HsPrelude'HsInt'is_le a b = a <= (b :: Int)
b'HsPrelude'HsInt'is_gt a b = a > (b :: Int)
b'HsPrelude'HsInt'is_ge a b = a >= (b :: Int)
b'HsPrelude'HsInt'max a b = max a (b :: Int)
b'HsPrelude'HsInt'min a b = min a (b :: Int)
b'HsPrelude'HsInt'succ a = a + 1 :: Int
b'HsPrelude'HsInt'pred a = a - 1 :: Int
b'HsPrelude'HsInt'even a = even (a :: Int)
b'HsPrelude'HsInt'odd a = odd (a :: Int)
b'HsPrelude'HsInt'show a = show (a :: Int)
b'HsPrelude'HsInt'count a = max 0 (a :: Int)
b'HsPrelude'HsInt'mul'sign neg n = if neg then negate n else n :: Int
b'HsPrelude'HsInt'quot a b = b'HsPrelude'HsInt'mul'sign ((a < 0) /= (b < 0)) (b'Nat'div (abs a) (abs b))
b'HsPrelude'HsInt'rem a b = b'HsPrelude'HsInt'mul'sign (a < 0) (b'Nat'mod (abs a) (abs b))
b'HsPrelude'HsInt'div a b = let { q = b'HsPrelude'HsInt'quot a b; r = b'HsPrelude'HsInt'rem a b } in if r /= 0 && ((a < 0) /= (b < 0)) then q - 1 else q
b'HsPrelude'HsInt'mod a b = let r = b'HsPrelude'HsInt'rem a b in if r /= 0 && ((r < 0) /= (b < 0)) then r + b else r
b'HsPrelude'HsInt'pow a e = a ^ abs (e :: Int) :: Int
b'HsPrelude'HsInt'gcd a b = gcd a (b :: Int)
b'HsPrelude'HsInt'lcm a b = lcm a (b :: Int)
b'HsPrelude'HsInt'range a b = [a .. b :: Int]

-- the prelude's partial functions, each a failure value (Left GHC's
-- message) where GHC throws (bend/Prelude.bend, "Partial functions")
b'HsPrelude'HsList'error msg = Left msg
b'HsPrelude'HsList'undefined = Left "Prelude.undefined"
b'HsPrelude'HsList'head xs = case xs of { [] -> Left "Prelude.head: empty list"; (x : _) -> Right x }
b'HsPrelude'HsList'tail xs = case xs of { [] -> Left "Prelude.tail: empty list"; (_ : t) -> Right t }
b'HsPrelude'HsList'last xs = case xs of { [] -> Left "Prelude.last: empty list"; _ -> Right (last xs) }
b'HsPrelude'HsList'init xs = case xs of { [] -> Left "Prelude.init: empty list"; _ -> Right (init xs) }
b'HsPrelude'HsList'fromJust m = case m of { Nothing -> Left "Maybe.fromJust: Nothing"; Just x -> Right x }
b'maxgo cmp x t = foldl (\a b -> case cmp a b of { GT -> a; _ -> b }) x t
b'mingo cmp x t = foldl (\a b -> case cmp a b of { GT -> b; _ -> a }) x t
b'HsPrelude'HsList'maximum cmp xs = case xs of { [] -> Left "Prelude.maximum: empty list"; (x : t) -> Right (b'maxgo cmp x t) }
b'HsPrelude'HsList'minimum cmp xs = case xs of { [] -> Left "Prelude.minimum: empty list"; (x : t) -> Right (b'mingo cmp x t) }
b'HsPrelude'HsList'maximumBy cmp xs = case xs of { [] -> Left "maximumBy: empty structure"; (x : t) -> Right (b'maxgo cmp x t) }
b'HsPrelude'HsList'minimumBy cmp xs = case xs of { [] -> Left "minimumBy: empty structure"; (x : t) -> Right (b'mingo cmp x t) }
b'HsPrelude'HsList'foldr1 f xs = case xs of { [] -> Left "Prelude.foldr1: empty list"; _ -> Right (foldr1 f xs) }
b'HsPrelude'HsList'foldl1 f xs = case xs of { [] -> Left "Prelude.foldl1: empty list"; _ -> Right (foldl1 f xs) }
b'HsPrelude'HsList'index xs n = if n < 0 then Left "Prelude.!!: negative index" else case drop n xs of { [] -> Left "Prelude.!!: index too large"; (x : _) -> Right x }

-- mapM and its kin at Maybe and at Either (HsPrelude.HsList.maybe.NAME,
-- HsPrelude.HsList.either.NAME)
b'HsPrelude'HsList'maybe'mapm f xs = mapM f xs
b'HsPrelude'HsList'maybe'mapm_ f xs = mapM_ f xs
b'HsPrelude'HsList'maybe'seq xs = sequence xs
b'HsPrelude'HsList'maybe'cons r rest = (:) <$> r <*> rest
b'HsPrelude'HsList'maybe'then r rest = r >> rest
b'HsPrelude'HsList'maybe'filterm p xs = case xs of { [] -> Just []; (x : t) -> p x >>= \k -> (if k then (x :) else id) <$> b'HsPrelude'HsList'maybe'filterm p t }
b'HsPrelude'HsList'maybe'foldm f xs z = foldl (\acc h -> acc >>= \a -> f a h) (Just z) xs
b'HsPrelude'HsList'maybe'zipwithm_ f xs ys = sequence_ (zipWith f xs ys)
b'HsPrelude'HsList'either'mapm f xs = mapM f xs
b'HsPrelude'HsList'either'mapm_ f xs = mapM_ f xs
b'HsPrelude'HsList'either'seq xs = sequence xs
b'HsPrelude'HsList'either'cons r rest = (:) <$> r <*> rest
b'HsPrelude'HsList'either'then r rest = r >> rest
b'HsPrelude'HsList'either'filterm p xs = case xs of { [] -> Right []; (x : t) -> p x >>= \k -> (if k then (x :) else id) <$> b'HsPrelude'HsList'either'filterm p t }
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

-- the prelude's recursion-scheme types (HsPrelude.Fix, .Cofree, .CofreeF
-- and its twin .CofreeF.fn), a type function F as Haskell's f
newtype B'HsPrelude'Fix f = B'HsPrelude'Fix'Fix (f (B'HsPrelude'Fix f))
data B'HsPrelude'Cofree f a = B'HsPrelude'Cofree'Cofree a (f (B'HsPrelude'Cofree f a))
data B'HsPrelude'CofreeF f a b = B'HsPrelude'CofreeF'CofreeF a (f b)
data B'HsPrelude'CofreeF'fn f a b = B'HsPrelude'CofreeF'fn'CofreeF a (f b)
b'HsPrelude'Fix'unFix (B'HsPrelude'Fix'Fix y) = y
b'HsPrelude'Cofree'project (B'HsPrelude'Cofree'Cofree h t) = B'HsPrelude'CofreeF'CofreeF h t
b'HsPrelude'Cofree'embed (B'HsPrelude'CofreeF'CofreeF h t) = B'HsPrelude'Cofree'Cofree h t
