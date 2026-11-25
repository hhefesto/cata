-- BendPc: the Haskell meaning of prelude/HsPc.bend (HsPrelude.HsPc.NAME,
-- cata's model of Text.Megaparsec's Parsec Void String), for bend2hs: each
-- def as the Bend one, its type arguments erased and its other arguments in
-- Bend's order; each data type with Bend's constructors, B' and the name
-- with its dots as primes, a record's one constructor named as its type.
-- A parser is a function of the state to a reply.  BendRt re-exports this
-- module.  tests/pc/rt.sh checks it against megaparsec (Oracle.hs's 28
-- parsers, the same texts).
--
-- One def differs inside: the escapes' table (lit.*) keeps a character as
-- its code, an Int, where Bend keeps a Char made from a U32; a code past
-- U+10FFFF (lit.num's cap, 1114112) is no Char in Haskell, and lit.code
-- refuses it before a Char is made, as Bend's does.
module BendPc where

import Prelude
import qualified Data.Char as DC
import Data.List (genericLength, genericReplicate)
import Numeric.Natural (Natural)
import Data.Word (Word32)

-- Bend's types (G writes B' and the name)
type B'Nat = Natural
type B'U32 = Word32
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
type B'HsPrelude'HsInt = Integer

data B'HsPrelude'HsPcItem
  = B'HsPrelude'HsPcItem'Tokens [Char]
  | B'HsPrelude'HsPcItem'Label [Char]
  | B'HsPrelude'HsPcItem'Eoi
  deriving (Eq, Show)

data B'HsPrelude'HsPcFancy
  = B'HsPrelude'HsPcFancy'Fail [Char]
  | B'HsPrelude'HsPcFancy'Indent Ordering Natural Natural
  deriving (Eq, Show)

data B'HsPrelude'HsPcError
  = B'HsPrelude'HsPcError'Trivial Natural (Maybe B'HsPrelude'HsPcItem) [B'HsPrelude'HsPcItem]
  | B'HsPrelude'HsPcError'Fancy Natural [B'HsPrelude'HsPcFancy]
  deriving (Eq, Show)

-- the input left, its offset, the line and column there, the source's name
data B'HsPrelude'HsPcSt = B'HsPrelude'HsPcSt [Char] Natural Natural Natural [Char]
  deriving (Eq, Show)

data B'HsPrelude'HsPcRes a
  = B'HsPrelude'HsPcRes'Ok a B'HsPrelude'HsPcSt [B'HsPrelude'HsPcItem]
  | B'HsPrelude'HsPcRes'Bad B'HsPrelude'HsPcError B'HsPrelude'HsPcSt
  deriving (Eq, Show)

data B'HsPrelude'HsPcRep a = B'HsPrelude'HsPcRep Bool (B'HsPrelude'HsPcRes a)
  deriving (Eq, Show)

data B'HsPrelude'HsPcPos = B'HsPrelude'HsPcPos [Char] Natural Natural
  deriving (Eq, Show)

data B'HsPrelude'HsPcBundle = B'HsPrelude'HsPcBundle B'HsPrelude'HsPcError [Char] [Char]
  deriving (Eq, Show)

data B'HsPrelude'HsPcAt = B'HsPrelude'HsPcAt Natural Natural [Char] [Char]
  deriving (Eq, Show)

-- Nat.sub: stops at 0
pc'nsub :: Natural -> Natural -> Natural
pc'nsub a b = if a < b then 0 else a - b

-- Sets as ascending lists ----------------------------------------------------

b'HsPrelude'HsPc'cmp'cmp :: B'Cmp -> B'Cmp -> B'Cmp
b'HsPrelude'HsPc'cmp'cmp a b = case (a, b) of
  (LT, LT) -> EQ
  (LT, _) -> LT
  (EQ, LT) -> GT
  (EQ, EQ) -> EQ
  (EQ, GT) -> LT
  (GT, GT) -> EQ
  (GT, _) -> GT

b'HsPrelude'HsPc'cmp'then :: B'Cmp -> B'Cmp -> B'Cmp
b'HsPrelude'HsPc'cmp'then a b = case a of { EQ -> b; o -> o }

-- HsCmp.list at HsCmp.char: lexicographic, by code
b'HsPrelude'HsPc'cmp'str :: (B'List B'Char) -> (B'List B'Char) -> B'Cmp
b'HsPrelude'HsPc'cmp'str a b = compare a b

b'HsPrelude'HsPc'str'eq :: (B'List B'Char) -> (B'List B'Char) -> B'Bool
b'HsPrelude'HsPc'str'eq xs ys = case (xs, ys) of
  ([], []) -> True
  (x : xt, y : yt) -> x == y && b'HsPrelude'HsPc'str'eq xt yt
  _ -> False

b'HsPrelude'HsPc'cmp'item :: B'HsPrelude'HsPcItem -> B'HsPrelude'HsPcItem -> B'Cmp
b'HsPrelude'HsPc'cmp'item a b = case (a, b) of
  (B'HsPrelude'HsPcItem'Tokens x, B'HsPrelude'HsPcItem'Tokens y) -> b'HsPrelude'HsPc'cmp'str x y
  (B'HsPrelude'HsPcItem'Tokens _, _) -> LT
  (B'HsPrelude'HsPcItem'Label _, B'HsPrelude'HsPcItem'Tokens _) -> GT
  (B'HsPrelude'HsPcItem'Label x, B'HsPrelude'HsPcItem'Label y) -> b'HsPrelude'HsPc'cmp'str x y
  (B'HsPrelude'HsPcItem'Label _, B'HsPrelude'HsPcItem'Eoi) -> LT
  (B'HsPrelude'HsPcItem'Eoi, B'HsPrelude'HsPcItem'Eoi) -> EQ
  (B'HsPrelude'HsPcItem'Eoi, _) -> GT

b'HsPrelude'HsPc'cmp'fancy :: B'HsPrelude'HsPcFancy -> B'HsPrelude'HsPcFancy -> B'Cmp
b'HsPrelude'HsPc'cmp'fancy a b = case (a, b) of
  (B'HsPrelude'HsPcFancy'Fail x, B'HsPrelude'HsPcFancy'Fail y) -> b'HsPrelude'HsPc'cmp'str x y
  (B'HsPrelude'HsPcFancy'Fail _, _) -> LT
  (B'HsPrelude'HsPcFancy'Indent _ _ _, B'HsPrelude'HsPcFancy'Fail _) -> GT
  (B'HsPrelude'HsPcFancy'Indent o1 r1 a1, B'HsPrelude'HsPcFancy'Indent o2 r2 a2) ->
    b'HsPrelude'HsPc'cmp'then (b'HsPrelude'HsPc'cmp'cmp o1 o2) (b'HsPrelude'HsPc'cmp'then (compare r1 r2) (compare a1 a2))

-- HsCmp.on c lt eq gt
pc'on :: Ordering -> r -> r -> r -> r
pc'on c lt eq gt = case c of { LT -> lt; EQ -> eq; GT -> gt }

b'HsPrelude'HsPc'iset'ins :: B'HsPrelude'HsPcItem -> (B'List B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'iset'ins x xs = case xs of
  [] -> [x]
  h : t -> pc'on (b'HsPrelude'HsPc'cmp'item x h) (x : h : t) (h : t) (h : b'HsPrelude'HsPc'iset'ins x t)

b'HsPrelude'HsPc'iset'union :: (B'List B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'iset'union xs ys = case xs of
  [] -> ys
  h : t -> b'HsPrelude'HsPc'iset'ins h (b'HsPrelude'HsPc'iset'union t ys)

b'HsPrelude'HsPc'fset'ins :: B'HsPrelude'HsPcFancy -> (B'List B'HsPrelude'HsPcFancy) -> (B'List B'HsPrelude'HsPcFancy)
b'HsPrelude'HsPc'fset'ins x xs = case xs of
  [] -> [x]
  h : t -> pc'on (b'HsPrelude'HsPc'cmp'fancy x h) (x : h : t) (h : t) (h : b'HsPrelude'HsPc'fset'ins x t)

b'HsPrelude'HsPc'fset'union :: (B'List B'HsPrelude'HsPcFancy) -> (B'List B'HsPrelude'HsPcFancy) -> (B'List B'HsPrelude'HsPcFancy)
b'HsPrelude'HsPc'fset'union xs ys = case xs of
  [] -> ys
  h : t -> b'HsPrelude'HsPc'fset'ins h (b'HsPrelude'HsPc'fset'union t ys)

b'HsPrelude'HsPc'sset'ins :: (B'List B'Char) -> (B'List (B'List B'Char)) -> (B'List (B'List B'Char))
b'HsPrelude'HsPc'sset'ins x xs = case xs of
  [] -> [x]
  h : t -> pc'on (b'HsPrelude'HsPc'cmp'str x h) (x : h : t) (h : t) (h : b'HsPrelude'HsPc'sset'ins x t)

b'HsPrelude'HsPc'item'max :: B'HsPrelude'HsPcItem -> B'HsPrelude'HsPcItem -> B'HsPrelude'HsPcItem
b'HsPrelude'HsPc'item'max a b = pc'on (b'HsPrelude'HsPc'cmp'item a b) b b a

b'HsPrelude'HsPc'un'merge :: (B'Maybe B'HsPrelude'HsPcItem) -> (B'Maybe B'HsPrelude'HsPcItem) -> (B'Maybe B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'un'merge a b = case (a, b) of
  (Nothing, y) -> y
  (Just x, Nothing) -> Just x
  (Just x, Just y) -> Just (b'HsPrelude'HsPc'item'max x y)

b'HsPrelude'HsPc'err'off :: B'HsPrelude'HsPcError -> B'Nat
b'HsPrelude'HsPc'err'off e = case e of
  B'HsPrelude'HsPcError'Trivial o _ _ -> o
  B'HsPrelude'HsPcError'Fancy o _ -> o

b'HsPrelude'HsPc'err'same :: B'HsPrelude'HsPcError -> B'HsPrelude'HsPcError -> B'HsPrelude'HsPcError
b'HsPrelude'HsPc'err'same e1 e2 = case (e1, e2) of
  (B'HsPrelude'HsPcError'Trivial s1 u1 p1, B'HsPrelude'HsPcError'Trivial _ u2 p2) ->
    B'HsPrelude'HsPcError'Trivial s1 (b'HsPrelude'HsPc'un'merge u1 u2) (b'HsPrelude'HsPc'iset'union p1 p2)
  (B'HsPrelude'HsPcError'Fancy s1 x1, B'HsPrelude'HsPcError'Trivial _ _ _) -> B'HsPrelude'HsPcError'Fancy s1 x1
  (B'HsPrelude'HsPcError'Trivial _ _ _, B'HsPrelude'HsPcError'Fancy s2 x2) -> B'HsPrelude'HsPcError'Fancy s2 x2
  (B'HsPrelude'HsPcError'Fancy s1 x1, B'HsPrelude'HsPcError'Fancy _ x2) ->
    B'HsPrelude'HsPcError'Fancy s1 (b'HsPrelude'HsPc'fset'union x1 x2)

b'HsPrelude'HsPc'err'merge :: B'HsPrelude'HsPcError -> B'HsPrelude'HsPcError -> B'HsPrelude'HsPcError
b'HsPrelude'HsPc'err'merge e1 e2 =
  pc'on (compare (b'HsPrelude'HsPc'err'off e1) (b'HsPrelude'HsPc'err'off e2)) e2 (b'HsPrelude'HsPc'err'same e1 e2) e1

b'HsPrelude'HsPc'st'off :: B'HsPrelude'HsPcSt -> B'Nat
b'HsPrelude'HsPc'st'off (B'HsPrelude'HsPcSt _ o _ _ _) = o

b'HsPrelude'HsPc'longest :: B'HsPrelude'HsPcSt -> B'HsPrelude'HsPcSt -> B'HsPrelude'HsPcSt
b'HsPrelude'HsPc'longest s1 s2 = if b'HsPrelude'HsPc'st'off s1 > b'HsPrelude'HsPc'st'off s2 then s1 else s2

b'HsPrelude'HsPc'hints :: B'Nat -> B'HsPrelude'HsPcError -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'hints o e = case e of
  B'HsPrelude'HsPcError'Trivial eo _ ps -> if o == eo then ps else []
  B'HsPrelude'HsPcError'Fancy _ _ -> []

b'HsPrelude'HsPc'err'hint :: (B'List B'HsPrelude'HsPcItem) -> B'HsPrelude'HsPcError -> B'HsPrelude'HsPcError
b'HsPrelude'HsPc'err'hint hs e = case e of
  B'HsPrelude'HsPcError'Trivial o u ps -> B'HsPrelude'HsPcError'Trivial o u (b'HsPrelude'HsPc'iset'union ps hs)
  f -> f

-- The core --------------------------------------------------------------------

type B'HsPrelude'HsPc'P a = B'HsPrelude'HsPcSt -> B'HsPrelude'HsPcRep a

b'HsPrelude'HsPc'pure :: a -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'pure x = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok x s [])

b'HsPrelude'HsPc'res'hint :: (B'List B'HsPrelude'HsPcItem) -> (B'HsPrelude'HsPcRes b) -> (B'HsPrelude'HsPcRes b)
b'HsPrelude'HsPc'res'hint hs r = case r of
  B'HsPrelude'HsPcRes'Ok x s h2 -> B'HsPrelude'HsPcRes'Ok x s (b'HsPrelude'HsPc'iset'union hs h2)
  B'HsPrelude'HsPcRes'Bad e s -> B'HsPrelude'HsPcRes'Bad (b'HsPrelude'HsPc'err'hint hs e) s

b'HsPrelude'HsPc'bind'k :: B'Bool -> (B'List B'HsPrelude'HsPcItem) -> (B'HsPrelude'HsPcRep b) -> (B'HsPrelude'HsPcRep b)
b'HsPrelude'HsPc'bind'k c1 hs r = case r of
  B'HsPrelude'HsPcRep True r2 -> B'HsPrelude'HsPcRep True r2
  B'HsPrelude'HsPcRep False r2 -> B'HsPrelude'HsPcRep c1 (b'HsPrelude'HsPc'res'hint hs r2)

b'HsPrelude'HsPc'bind'go :: (B'HsPrelude'HsPcRep a) -> (a -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)) -> (B'HsPrelude'HsPcRep b)
b'HsPrelude'HsPc'bind'go r k = case r of
  B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Ok x s hs) -> b'HsPrelude'HsPc'bind'k c hs (k x s)
  B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Bad e s) -> B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Bad e s)

b'HsPrelude'HsPc'bind :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> (a -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)
b'HsPrelude'HsPc'bind m k = \s -> b'HsPrelude'HsPc'bind'go (m s) k

b'HsPrelude'HsPc'map'go :: (a -> b) -> (B'HsPrelude'HsPcRep a) -> (B'HsPrelude'HsPcRep b)
b'HsPrelude'HsPc'map'go f r = case r of
  B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Ok x s hs) -> B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Ok (f x) s hs)
  B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Bad e s) -> B'HsPrelude'HsPcRep c (B'HsPrelude'HsPcRes'Bad e s)

b'HsPrelude'HsPc'map :: (a -> b) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)
b'HsPrelude'HsPc'map f m = \s -> b'HsPrelude'HsPc'map'go f (m s)

-- m >> n, m <* n, x <$ m, void m
b'HsPrelude'HsPc'then :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)
b'HsPrelude'HsPc'then m n = b'HsPrelude'HsPc'bind m (\_ -> n)

b'HsPrelude'HsPc'left :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'left m n = b'HsPrelude'HsPc'bind m (\x -> b'HsPrelude'HsPc'map (\_ -> x) n)

b'HsPrelude'HsPc'const :: a -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep b)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'const x m = b'HsPrelude'HsPc'map (\_ -> x) m

b'HsPrelude'HsPc'void :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'void m = b'HsPrelude'HsPc'map (\_ -> ()) m

-- m <|> n: n at the state m began at, if m failed without consuming
b'HsPrelude'HsPc'alt'n :: B'HsPrelude'HsPcError -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a) -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'alt'n err ms r = case r of
  B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok x s hs) -> B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok x s hs)
  B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Bad e s) ->
    B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Bad (b'HsPrelude'HsPc'err'merge e err) (b'HsPrelude'HsPc'longest ms s))
  B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok x s hs) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok x s (b'HsPrelude'HsPc'iset'union (b'HsPrelude'HsPc'hints (b'HsPrelude'HsPc'st'off s) err) hs))
  B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad e s) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (b'HsPrelude'HsPc'err'merge e err) (b'HsPrelude'HsPc'longest ms s))

b'HsPrelude'HsPc'alt'go :: (B'HsPrelude'HsPcRep a) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'alt'go r n s = case r of
  B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad e ms) -> b'HsPrelude'HsPc'alt'n e ms (n s)
  other -> other

b'HsPrelude'HsPc'alt :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'alt m n = \s -> b'HsPrelude'HsPc'alt'go (m s) n s

b'HsPrelude'HsPc'st'err :: B'HsPrelude'HsPcSt -> B'HsPrelude'HsPcError -> (B'HsPrelude'HsPcRes B'Unit)
b'HsPrelude'HsPc'st'err s e = B'HsPrelude'HsPcRes'Bad e s

-- empty: fails where it is, expecting nothing
b'HsPrelude'HsPc'empty :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'empty = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) Nothing []) s)

b'HsPrelude'HsPc'fail :: (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'fail msg = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Fancy (b'HsPrelude'HsPc'st'off s) [B'HsPrelude'HsPcFancy'Fail msg]) s)

-- the parser no run reaches (where Haskell's loops forever)
b'HsPrelude'HsPc'bottom :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'bottom = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Fancy (b'HsPrelude'HsPc'st'off s) []) s)

b'HsPrelude'HsPc'try'go :: (B'HsPrelude'HsPcRep a) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'try'go r s = case r of
  B'HsPrelude'HsPcRep _ (B'HsPrelude'HsPcRes'Bad e _) -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad e s)
  other -> other

b'HsPrelude'HsPc'try :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'try p = \s -> b'HsPrelude'HsPc'try'go (p s) s

-- label l p (p <?> l); hidden is label ""
b'HsPrelude'HsPc'label'refresh :: (B'Maybe B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'label'refresh el hs = case (el, hs) of
  (Nothing, _) -> []
  (Just _, []) -> []
  (Just m, _) -> [m]

b'HsPrelude'HsPc'label'ex :: (B'Maybe B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'label'ex el = case el of { Nothing -> []; Just m -> [m] }

b'HsPrelude'HsPc'label'go :: (B'Maybe B'HsPrelude'HsPcItem) -> (B'HsPrelude'HsPcRep a) -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'label'go el r = case r of
  B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok x s hs) ->
    B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok x s (case el of { Nothing -> []; Just _ -> hs }))
  B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok x s hs) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok x s (b'HsPrelude'HsPc'label'refresh el hs))
  B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial o u _) s) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial o u (b'HsPrelude'HsPc'label'ex el)) s)
  other -> other

b'HsPrelude'HsPc'label'of :: (B'List B'Char) -> (B'Maybe B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'label'of l = case l of { [] -> Nothing; _ -> Just (B'HsPrelude'HsPcItem'Label l) }

b'HsPrelude'HsPc'label :: (B'List B'Char) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'label l p = \s -> b'HsPrelude'HsPc'label'go (b'HsPrelude'HsPc'label'of l) (p s)

b'HsPrelude'HsPc'hidden :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'hidden p = b'HsPrelude'HsPc'label [] p

b'HsPrelude'HsPc'labelf :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'labelf p l = b'HsPrelude'HsPc'label l p

-- Tokens ------------------------------------------------------------------------

-- a tab goes to the next multiple of 8, plus 1
b'HsPrelude'HsPc'col'tab :: B'Nat -> B'Nat
b'HsPrelude'HsPc'col'tab c = pc'nsub (c + 8) (pc'nsub c 1 `mod` 8)

b'HsPrelude'HsPc'adv :: B'Char -> (B'List B'Char) -> B'Nat -> B'Nat -> B'Nat -> (B'List B'Char) -> B'HsPrelude'HsPcSt
b'HsPrelude'HsPc'adv ch rest o l c n =
  let k = fromIntegral (DC.ord ch)
  in if k == 10 then B'HsPrelude'HsPcSt rest (o + 1) (l + 1) 1 n
     else B'HsPrelude'HsPcSt rest (o + 1) l (if k == 9 then b'HsPrelude'HsPc'col'tab c else c + 1) n

b'HsPrelude'HsPc'sat'in :: (B'Char -> B'Bool) -> (B'List B'HsPrelude'HsPcItem) -> (B'List B'Char) -> B'Nat -> B'Nat -> B'Nat -> (B'List B'Char) -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'sat'in f ps inp o l c n = case inp of
  [] -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial o (Just B'HsPrelude'HsPcItem'Eoi) ps) (B'HsPrelude'HsPcSt [] o l c n))
  h : t ->
    if f h then B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok h (b'HsPrelude'HsPc'adv h t o l c n) [])
    else B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial o (Just (B'HsPrelude'HsPcItem'Tokens [h])) ps) (B'HsPrelude'HsPcSt (h : t) o l c n))

b'HsPrelude'HsPc'sat'go :: (B'Char -> B'Bool) -> (B'List B'HsPrelude'HsPcItem) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'sat'go f ps (B'HsPrelude'HsPcSt i o l c n) = b'HsPrelude'HsPc'sat'in f ps i o l c n

b'HsPrelude'HsPc'satisfy :: (B'Char -> B'Bool) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'satisfy f = \s -> b'HsPrelude'HsPc'sat'go f [] s

b'HsPrelude'HsPc'char :: B'Char -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'char ch = \s -> b'HsPrelude'HsPc'sat'go (\x -> x == ch) [B'HsPrelude'HsPcItem'Tokens [ch]] s

b'HsPrelude'HsPc'anySingle :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'anySingle = b'HsPrelude'HsPc'satisfy (\_ -> True)

-- string (tokens (==)): all of it or nothing consumed
b'HsPrelude'HsPc'split'take :: B'Nat -> (B'List B'Char) -> (B'List B'Char)
b'HsPrelude'HsPc'split'take n xs = case xs of
  h : t | n >= 1 -> h : b'HsPrelude'HsPc'split'take (n - 1) t
  _ -> []

b'HsPrelude'HsPc'split'drop :: B'Nat -> (B'List B'Char) -> (B'List B'Char)
b'HsPrelude'HsPc'split'drop n xs = case xs of
  _ : t | n >= 1 -> b'HsPrelude'HsPc'split'drop (n - 1) t
  ys -> ys

b'HsPrelude'HsPc'split'cons :: B'Char -> (B'List B'Char) -> (B'List B'Char) -> (B'Maybe (B'Sigma (B'List B'Char) (B'List B'Char)))
b'HsPrelude'HsPc'split'cons h a b = Just (h : a, b)

b'HsPrelude'HsPc'split :: B'Nat -> (B'List B'Char) -> (B'Maybe (B'Sigma (B'List B'Char) (B'List B'Char)))
b'HsPrelude'HsPc'split n xs
  | n == 0 = Just ([], xs)
  | otherwise = case xs of
      [] -> Nothing
      h : t -> b'HsPrelude'HsPc'split'cons h (b'HsPrelude'HsPc'split'take (n - 1) t) (b'HsPrelude'HsPc'split'drop (n - 1) t)

-- the state after the characters ts
b'HsPrelude'HsPc'advs :: (B'List B'Char) -> B'HsPrelude'HsPcSt -> B'HsPrelude'HsPcSt
b'HsPrelude'HsPc'advs ts s = case (ts, s) of
  ([], s1) -> s1
  (h : t, B'HsPrelude'HsPcSt _ o l c n) -> b'HsPrelude'HsPc'advs t (b'HsPrelude'HsPc'adv h [] o l c n)

b'HsPrelude'HsPc'st'input :: B'HsPrelude'HsPcSt -> (B'List B'Char) -> B'HsPrelude'HsPcSt
b'HsPrelude'HsPc'st'input (B'HsPrelude'HsPcSt _ o l c n) i = B'HsPrelude'HsPcSt i o l c n

b'HsPrelude'HsPc'str'cmp :: (B'List B'Char) -> (B'Maybe (B'Sigma (B'List B'Char) (B'List B'Char))) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'str'cmp tts m s = case m of
  Nothing -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just B'HsPrelude'HsPcItem'Eoi) [B'HsPrelude'HsPcItem'Tokens tts]) s)
  Just (got, rest) ->
    if b'HsPrelude'HsPc'str'eq tts got
      then B'HsPrelude'HsPcRep (not (null tts)) (B'HsPrelude'HsPcRes'Ok got (b'HsPrelude'HsPc'st'input (b'HsPrelude'HsPc'advs got s) rest) [])
      else B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just (B'HsPrelude'HsPcItem'Tokens got)) [B'HsPrelude'HsPcItem'Tokens tts]) s)

b'HsPrelude'HsPc'st'inp :: B'HsPrelude'HsPcSt -> (B'List B'Char)
b'HsPrelude'HsPc'st'inp (B'HsPrelude'HsPcSt i _ _ _ _) = i

b'HsPrelude'HsPc'string :: (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'string tts = \s -> b'HsPrelude'HsPc'str'cmp tts (b'HsPrelude'HsPc'split (genericLength tts) (b'HsPrelude'HsPc'st'inp s)) s

b'HsPrelude'HsPc'eof'in :: (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'eof'in i s = case i of
  [] -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok () s [])
  h : _ -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just (B'HsPrelude'HsPcItem'Tokens [h])) [B'HsPrelude'HsPcItem'Eoi]) s)

b'HsPrelude'HsPc'eof :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'eof = \s -> b'HsPrelude'HsPc'eof'in (b'HsPrelude'HsPc'st'inp s) s

-- what is next, as an error's unexpected item
b'HsPrelude'HsPc'next'item :: (B'List B'Char) -> B'HsPrelude'HsPcItem
b'HsPrelude'HsPc'next'item i = case i of
  [] -> B'HsPrelude'HsPcItem'Eoi
  h : _ -> B'HsPrelude'HsPcItem'Tokens [h]

b'HsPrelude'HsPc'nfb'go :: (B'HsPrelude'HsPcRep a) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'nfb'go r s = case r of
  B'HsPrelude'HsPcRep _ (B'HsPrelude'HsPcRes'Ok _ _ _) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just (b'HsPrelude'HsPc'next'item (b'HsPrelude'HsPc'st'inp s))) []) s)
  B'HsPrelude'HsPcRep _ (B'HsPrelude'HsPcRes'Bad _ _) -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok () s [])

b'HsPrelude'HsPc'notFollowedBy :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'notFollowedBy p = \s -> b'HsPrelude'HsPc'nfb'go (p s) s

b'HsPrelude'HsPc'look'go :: (B'HsPrelude'HsPcRep a) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'look'go r s = case r of
  B'HsPrelude'HsPcRep _ (B'HsPrelude'HsPcRes'Ok x _ _) -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok x s [])
  other -> other

b'HsPrelude'HsPc'lookAhead :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'lookAhead p = \s -> b'HsPrelude'HsPc'look'go (p s) s

-- HsInt.Pos{offset}: an Int
b'HsPrelude'HsPc'getOffset :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'HsPrelude'HsInt)
b'HsPrelude'HsPc'getOffset = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok (toInteger (b'HsPrelude'HsPc'st'off s)) s [])

b'HsPrelude'HsPc'st'pos :: B'HsPrelude'HsPcSt -> B'HsPrelude'HsPcPos
b'HsPrelude'HsPc'st'pos (B'HsPrelude'HsPcSt _ _ l c n) = B'HsPrelude'HsPcPos n l c

b'HsPrelude'HsPc'getSourcePos :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'HsPrelude'HsPcPos)
b'HsPrelude'HsPc'getSourcePos = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Ok (b'HsPrelude'HsPc'st'pos s) s [])

-- takeWhileP and takeWhile1P: the longest prefix f takes
b'HsPrelude'HsPc'tw'go :: (B'Char -> B'Bool) -> (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'List B'Char) -> (B'Sigma (B'List B'Char) B'HsPrelude'HsPcSt)
b'HsPrelude'HsPc'tw'go f i s acc = case (i, s) of
  (h : t, B'HsPrelude'HsPcSt _ o l c n) ->
    if f h then b'HsPrelude'HsPc'tw'go f t (b'HsPrelude'HsPc'adv h t o l c n) (h : acc)
    else (reverse acc, B'HsPrelude'HsPcSt (h : t) o l c n)
  ([], s1) -> (reverse acc, s1)

b'HsPrelude'HsPc'tw'hs :: (B'Maybe (B'List B'Char)) -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'tw'hs ml = case ml of
  Just (h : t) -> [B'HsPrelude'HsPcItem'Label (h : t)]
  _ -> []

b'HsPrelude'HsPc'tw'rep :: (B'List B'HsPrelude'HsPcItem) -> (B'Sigma (B'List B'Char) B'HsPrelude'HsPcSt) -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'tw'rep hs (ts, s1) = B'HsPrelude'HsPcRep (not (null ts)) (B'HsPrelude'HsPcRes'Ok ts s1 hs)

b'HsPrelude'HsPc'takeWhileP :: (B'Char -> B'Bool) -> (B'Maybe (B'List B'Char)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'takeWhileP f ml = \s -> b'HsPrelude'HsPc'tw'rep (b'HsPrelude'HsPc'tw'hs ml) (b'HsPrelude'HsPc'tw'go f (b'HsPrelude'HsPc'st'inp s) s [])

b'HsPrelude'HsPc'tw1'rep :: (B'List B'HsPrelude'HsPcItem) -> (B'Sigma (B'List B'Char) B'HsPrelude'HsPcSt) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'tw1'rep hs p s = case p of
  ([], _) -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just (b'HsPrelude'HsPc'next'item (b'HsPrelude'HsPc'st'inp s))) hs) s)
  (ts, s1) -> B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok ts s1 hs)

b'HsPrelude'HsPc'takeWhile1P :: (B'Char -> B'Bool) -> (B'Maybe (B'List B'Char)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'takeWhile1P f ml = \s -> b'HsPrelude'HsPc'tw1'rep (b'HsPrelude'HsPc'tw'hs ml) (b'HsPrelude'HsPc'tw'go f (b'HsPrelude'HsPc'st'inp s) s []) s

-- Running ------------------------------------------------------------------------

b'HsPrelude'HsPc'st0 :: (B'List B'Char) -> (B'List B'Char) -> B'HsPrelude'HsPcSt
b'HsPrelude'HsPc'st0 name inp = B'HsPrelude'HsPcSt inp 0 1 1 name

b'HsPrelude'HsPc'run'go :: (B'HsPrelude'HsPcRep a) -> (B'List B'Char) -> (B'List B'Char) -> (B'Either B'HsPrelude'HsPcBundle a)
b'HsPrelude'HsPc'run'go r name inp = case r of
  B'HsPrelude'HsPcRep _ (B'HsPrelude'HsPcRes'Ok x _ _) -> Right x
  B'HsPrelude'HsPcRep _ (B'HsPrelude'HsPcRes'Bad e _) -> Left (B'HsPrelude'HsPcBundle e inp name)

b'HsPrelude'HsPc'runParser :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> (B'List B'Char) -> (B'List B'Char) -> (B'Either B'HsPrelude'HsPcBundle a)
b'HsPrelude'HsPc'runParser p name inp = b'HsPrelude'HsPc'run'go (p (b'HsPrelude'HsPc'st0 name inp)) name inp

-- a reply no run gives: fuel's default, where Haskell's would not stop
b'HsPrelude'HsPc'rep'default :: (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'rep'default = B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Fancy 0 []) (B'HsPrelude'HsPcSt [] 0 1 1 []))

b'HsPrelude'HsPc'optional :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'Maybe a))
b'HsPrelude'HsPc'optional p = b'HsPrelude'HsPc'alt (b'HsPrelude'HsPc'map Just p) (b'HsPrelude'HsPc'pure Nothing)

b'HsPrelude'HsPc'option :: a -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'option x p = b'HsPrelude'HsPc'alt p (b'HsPrelude'HsPc'pure x)

b'HsPrelude'HsPc'between :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep o)) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep c)) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'between o c p = b'HsPrelude'HsPc'left (b'HsPrelude'HsPc'then o p) c

b'HsPrelude'HsPc'lexeme :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)) -> (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'lexeme spc p = b'HsPrelude'HsPc'left p spc

b'HsPrelude'HsPc'symbol :: (B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)) -> (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep (B'List B'Char))
b'HsPrelude'HsPc'symbol spc w = b'HsPrelude'HsPc'left (b'HsPrelude'HsPc'string w) spc

b'HsPrelude'HsPc'space1 :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'space1 = b'HsPrelude'HsPc'void (b'HsPrelude'HsPc'takeWhile1P DC.isSpace (Just "white space"))

b'HsPrelude'HsPc'space :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'space = b'HsPrelude'HsPc'void (b'HsPrelude'HsPc'takeWhileP DC.isSpace (Just "white space"))

b'HsPrelude'HsPc'not'nl :: B'Char -> B'Bool
b'HsPrelude'HsPc'not'nl c = fromIntegral (DC.ord c) /= 10

b'HsPrelude'HsPc'skipLineComment :: (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Unit)
b'HsPrelude'HsPc'skipLineComment w =
  b'HsPrelude'HsPc'then (b'HsPrelude'HsPc'string w) (b'HsPrelude'HsPc'void (b'HsPrelude'HsPc'takeWhileP b'HsPrelude'HsPc'not'nl (Just "character")))

b'HsPrelude'HsPc'pos'name :: B'HsPrelude'HsPcPos -> (B'List B'Char)
b'HsPrelude'HsPc'pos'name (B'HsPrelude'HsPcPos n _ _) = n

b'HsPrelude'HsPc'pos'line :: B'HsPrelude'HsPcPos -> B'Nat
b'HsPrelude'HsPc'pos'line (B'HsPrelude'HsPcPos _ l _) = l

b'HsPrelude'HsPc'pos'col :: B'HsPrelude'HsPcPos -> B'Nat
b'HsPrelude'HsPc'pos'col (B'HsPrelude'HsPcPos _ _ c) = c

b'HsPrelude'HsPc'indentLevel :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Nat)
b'HsPrelude'HsPc'indentLevel = b'HsPrelude'HsPc'map b'HsPrelude'HsPc'pos'col b'HsPrelude'HsPc'getSourcePos

b'HsPrelude'HsPc'incorrectIndent :: B'Cmp -> B'Nat -> B'Nat -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'incorrectIndent o r a = \s ->
  B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Fancy (b'HsPrelude'HsPc'st'off s) [B'HsPrelude'HsPcFancy'Indent o r a]) s)

-- decimal = mkNum <$> takeWhile1P (Just "digit") isDigit <?> "integer"
b'HsPrelude'HsPc'digits :: (B'List B'Char) -> B'Nat -> B'Nat
b'HsPrelude'HsPc'digits xs acc = case xs of
  [] -> acc
  h : t -> b'HsPrelude'HsPc'digits t (acc * 10 + fromIntegral (fromIntegral (DC.ord h) - 48))

b'HsPrelude'HsPc'decimal :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'HsPrelude'HsInt)
b'HsPrelude'HsPc'decimal =
  b'HsPrelude'HsPc'label "integer" (b'HsPrelude'HsPc'map (\ds -> toInteger (b'HsPrelude'HsPc'digits ds 0)) (b'HsPrelude'HsPc'takeWhile1P DC.isDigit (Just "digit")))

b'HsPrelude'HsPc'unexpected :: B'HsPrelude'HsPcItem -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep a)
b'HsPrelude'HsPc'unexpected i = \s -> B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just i) []) s)

-- charLiteral: GHC's readLitChar on the next at most 10 characters, then
-- that many skipped.  A literal: its character's code and its length.
data B'HsPrelude'HsPcLit = B'HsPrelude'HsPcLit Word32 Natural
  deriving (Eq, Show)

b'HsPrelude'HsPc'lit'one :: B'U32 -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'one c =
  let k | c == 97 = 7
        | c == 98 = 8
        | c == 102 = 12
        | c == 110 = 10
        | c == 114 = 13
        | c == 116 = 9
        | c == 118 = 11
        | c == 92 || c == 34 || c == 39 = c
        | otherwise = 1114112
  in if k < 1114112 then Just (B'HsPrelude'HsPcLit k 2) else Nothing

-- the value of a digit in base b, if it is one (else 99)
b'HsPrelude'HsPc'lit'dig :: B'U32 -> B'U32 -> B'U32
b'HsPrelude'HsPc'lit'dig b c =
  let d | c >= 48 && c <= 57 = c - 48
        | c >= 97 && c <= 102 = c - 87
        | c >= 65 && c <= 70 = c - 55
        | otherwise = 99
  in if d < b then d else 99

-- the digits at the front, their value capped above the largest code
b'HsPrelude'HsPc'lit'num :: B'U32 -> (B'List B'Char) -> B'U32 -> B'Nat -> B'HsPrelude'HsPcLit
b'HsPrelude'HsPc'lit'num b xs v n = case xs of
  [] -> B'HsPrelude'HsPcLit v n
  h : t ->
    let d = b'HsPrelude'HsPc'lit'dig b (fromIntegral (DC.ord h))
    in if d < 99 then b'HsPrelude'HsPc'lit'num b t (min (v * b + d) 1114112) (n + 1) else B'HsPrelude'HsPcLit v n

b'HsPrelude'HsPc'lit'code :: B'HsPrelude'HsPcLit -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'code (B'HsPrelude'HsPcLit c n) = if c < 1114112 && n > 0 then Just (B'HsPrelude'HsPcLit c n) else Nothing

b'HsPrelude'HsPc'lit'at :: B'HsPrelude'HsPcLit -> B'Nat -> B'HsPrelude'HsPcLit
b'HsPrelude'HsPc'lit'at (B'HsPrelude'HsPcLit c n) k = B'HsPrelude'HsPcLit c (n + k)

b'HsPrelude'HsPc'lit'base :: B'U32 -> (B'List B'Char) -> B'Nat -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'base b xs k = fmap (\m -> b'HsPrelude'HsPc'lit'at m k) (b'HsPrelude'HsPc'lit'code (b'HsPrelude'HsPc'lit'num b xs 0 0))

-- \^X: X from @ to _ is its code less 64
b'HsPrelude'HsPc'lit'ctl :: (B'List B'Char) -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'ctl xs = case xs of
  h : _ -> let k = fromIntegral (DC.ord h) in if k >= 64 && k <= 95 then Just (B'HsPrelude'HsPcLit (k - 64) 3) else Nothing
  [] -> Nothing

-- the ASCII control names, SOH before SO (Text.Read.Lex tries it first)
b'HsPrelude'HsPc'lit'names :: (B'List B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'names =
  [ B'HsPrelude'HsPcLit c n
  | (c, n) <- [ (0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (7, 3), (8, 2), (9, 2), (10, 2), (11, 2), (12, 2), (13, 2), (14, 2), (15, 2)
              , (16, 3), (17, 3), (18, 3), (19, 3), (20, 3), (21, 3), (22, 3), (23, 3), (24, 3), (25, 2), (26, 3), (27, 3), (28, 2), (29, 2), (30, 2), (31, 2)
              , (32, 2), (127, 3) ] ]

b'HsPrelude'HsPc'lit'words :: (B'List (B'List B'Char))
b'HsPrelude'HsPc'lit'words =
  [ "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4"
  , "NAK", "SYN", "ETB", "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US", "SP", "DEL" ]

b'HsPrelude'HsPc'lit'prefix :: (B'List B'Char) -> (B'List B'Char) -> B'Bool
b'HsPrelude'HsPc'lit'prefix p xs = case (p, xs) of
  ([], _) -> True
  (a : pt, b : xt) -> a == b && b'HsPrelude'HsPc'lit'prefix pt xt
  _ -> False

b'HsPrelude'HsPc'lit'name :: (B'List (B'List B'Char)) -> (B'List B'HsPrelude'HsPcLit) -> (B'List B'Char) -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'name ws ls xs = case (ws, ls) of
  (w : wt, B'HsPrelude'HsPcLit c n : lt) ->
    if b'HsPrelude'HsPc'lit'prefix w xs then Just (B'HsPrelude'HsPcLit c (n + 1)) else b'HsPrelude'HsPc'lit'name wt lt xs
  _ -> Nothing

b'HsPrelude'HsPc'lit'esc :: B'Char -> (B'List B'Char) -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'esc h t =
  let k = fromIntegral (DC.ord h)
  in if k >= 48 && k <= 57 then b'HsPrelude'HsPc'lit'base 10 (h : t) 1
     else if k == 111 then b'HsPrelude'HsPc'lit'base 8 t 2
     else if k == 120 then b'HsPrelude'HsPc'lit'base 16 t 2
     else if k == 94 then b'HsPrelude'HsPc'lit'ctl t
     else case b'HsPrelude'HsPc'lit'one k of
       Just m -> Just m
       Nothing -> b'HsPrelude'HsPc'lit'name b'HsPrelude'HsPc'lit'words b'HsPrelude'HsPc'lit'names (h : t)

b'HsPrelude'HsPc'lit'after :: (B'List B'Char) -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'after xs = case xs of
  h : t -> b'HsPrelude'HsPc'lit'esc h t
  [] -> Nothing

b'HsPrelude'HsPc'lit'read :: (B'List B'Char) -> (B'Maybe B'HsPrelude'HsPcLit)
b'HsPrelude'HsPc'lit'read xs = case xs of
  h : t -> if fromIntegral (DC.ord h) == 92 then b'HsPrelude'HsPc'lit'after t else Just (B'HsPrelude'HsPcLit (fromIntegral (DC.ord h)) 1)
  [] -> Nothing

b'HsPrelude'HsPc'lit'got :: (B'Maybe B'HsPrelude'HsPcLit) -> (B'List B'Char) -> B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'lit'got m inp s = case (m, inp) of
  (Just (B'HsPrelude'HsPcLit c n), _) ->
    B'HsPrelude'HsPcRep True (B'HsPrelude'HsPcRes'Ok (DC.chr (fromIntegral c)) (b'HsPrelude'HsPc'st'input (b'HsPrelude'HsPc'advs (b'HsPrelude'HsPc'split'take n inp) s) (b'HsPrelude'HsPc'split'drop n inp)) [])
  (Nothing, h : _) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just (B'HsPrelude'HsPcItem'Tokens [h])) [B'HsPrelude'HsPcItem'Label "literal character"]) s)
  (Nothing, []) ->
    B'HsPrelude'HsPcRep False (B'HsPrelude'HsPcRes'Bad (B'HsPrelude'HsPcError'Trivial (b'HsPrelude'HsPc'st'off s) (Just B'HsPrelude'HsPcItem'Eoi) [B'HsPrelude'HsPcItem'Label "literal character"]) s)

b'HsPrelude'HsPc'charLiteral :: B'HsPrelude'HsPcSt -> (B'HsPrelude'HsPcRep B'Char)
b'HsPrelude'HsPc'charLiteral = \s ->
  b'HsPrelude'HsPc'lit'got (b'HsPrelude'HsPc'lit'read (b'HsPrelude'HsPc'split'take 10 (b'HsPrelude'HsPc'st'inp s))) (b'HsPrelude'HsPc'st'inp s) s

-- Pos and Int: unPos
b'HsPrelude'HsPc'unPos :: B'Nat -> B'HsPrelude'HsInt
b'HsPrelude'HsPc'unPos n = toInteger n

-- errorBundlePretty ----------------------------------------------------------

b'HsPrelude'HsPc'pp'walk :: B'Nat -> (B'List B'Char) -> B'Nat -> B'Nat -> (B'List B'Char) -> B'HsPrelude'HsPcAt
b'HsPrelude'HsPc'pp'walk n xs l c acc = case xs of
  h : t | n >= 1 ->
    let u = fromIntegral (DC.ord h)
        nl = u == 10
    in b'HsPrelude'HsPc'pp'walk (n - 1) t (if nl then l + 1 else l) (if nl then 1 else if u == 9 then b'HsPrelude'HsPc'col'tab c else c + 1) (if nl then [] else h : acc)
  ys -> B'HsPrelude'HsPcAt l c acc ys

b'HsPrelude'HsPc'pp'line :: (B'List B'Char) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'line xs = case xs of
  h : t -> if fromIntegral (DC.ord h) == 10 then [] else h : b'HsPrelude'HsPc'pp'line t
  [] -> []

-- expandTab 8
b'HsPrelude'HsPc'pp'tabs :: (B'List B'Char) -> B'Nat -> (B'List B'Char)
b'HsPrelude'HsPc'pp'tabs xs i = case xs of
  h : t ->
    let k = pc'nsub 8 (i `mod` 8)
        tab = fromIntegral (DC.ord h) == 9
    in (if tab then genericReplicate k ' ' else [h]) ++ b'HsPrelude'HsPc'pp'tabs t (if tab then i + k else i + 1)
  [] -> []

b'HsPrelude'HsPc'pp'nonempty :: (B'List B'Char) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'nonempty xs = case xs of { [] -> "<empty line>"; _ -> xs }

b'HsPrelude'HsPc'pp'str :: B'String -> (B'List B'Char)
b'HsPrelude'HsPc'pp'str s = s

b'HsPrelude'HsPc'pp'nat :: B'Nat -> (B'List B'Char)
b'HsPrelude'HsPc'pp'nat n = show n

-- charPretty' (Text.Megaparsec.Stream)
b'HsPrelude'HsPc'pp'names :: (B'List B'String)
b'HsPrelude'HsPc'pp'names =
  [ "null", "start of heading", "start of text", "end of text", "end of transmission", "enquiry", "acknowledge", "bell", "backspace", "tab"
  , "newline", "vertical tab", "form feed", "carriage return", "shift out", "shift in", "data link escape", "device control one"
  , "device control two", "device control three", "device control four", "negative acknowledge", "synchronous idle"
  , "end of transmission block", "cancel", "end of medium", "substitute", "escape", "file separator", "group separator"
  , "record separator", "unit separator" ]

b'HsPrelude'HsPc'pp'nth :: (B'List B'String) -> B'Nat -> (B'List B'Char)
b'HsPrelude'HsPc'pp'nth xs n = case xs of
  h : t -> if n == 0 then h else b'HsPrelude'HsPc'pp'nth t (n - 1)
  [] -> []

b'HsPrelude'HsPc'pp'cname :: B'Char -> (B'Maybe (B'List B'Char))
b'HsPrelude'HsPc'pp'cname c =
  let k = fromIntegral (DC.ord c)
  in if k < 32 then Just (b'HsPrelude'HsPc'pp'nth b'HsPrelude'HsPc'pp'names k)
     else if k == 127 then Just "delete"
     else if k == 160 then Just "non-breaking space"
     else Nothing

b'HsPrelude'HsPc'pp'char'at :: (B'Maybe (B'List B'Char)) -> B'Char -> (B'List B'Char)
b'HsPrelude'HsPc'pp'char'at m c = case m of { Just n -> n; Nothing -> ['\'', c, '\''] }

b'HsPrelude'HsPc'pp'char :: B'Char -> (B'List B'Char)
b'HsPrelude'HsPc'pp'char c = if fromIntegral (DC.ord c) == 32 then "space" else b'HsPrelude'HsPc'pp'char'at (b'HsPrelude'HsPc'pp'cname c) c

b'HsPrelude'HsPc'pp'inner'at :: (B'Maybe (B'List B'Char)) -> B'Char -> (B'List B'Char)
b'HsPrelude'HsPc'pp'inner'at m c = case m of { Just n -> ('<' : n) ++ ">"; Nothing -> [c] }

b'HsPrelude'HsPc'pp'inner :: (B'List B'Char) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'inner xs = case xs of
  h : t -> b'HsPrelude'HsPc'pp'inner'at (b'HsPrelude'HsPc'pp'cname h) h ++ b'HsPrelude'HsPc'pp'inner t
  [] -> []

b'HsPrelude'HsPc'pp'crlf :: (B'List B'Char) -> B'Bool
b'HsPrelude'HsPc'pp'crlf xs = case xs of
  [a, b] -> fromIntegral (DC.ord a) == 13 && fromIntegral (DC.ord b) == 10
  _ -> False

-- stringPretty
b'HsPrelude'HsPc'pp'tokens :: (B'List B'Char) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'tokens xs = case xs of
  [h] -> b'HsPrelude'HsPc'pp'char h
  ys -> if b'HsPrelude'HsPc'pp'crlf ys then "crlf newline" else ('"' : b'HsPrelude'HsPc'pp'inner ys) ++ "\""

b'HsPrelude'HsPc'pp'item :: B'HsPrelude'HsPcItem -> (B'List B'Char)
b'HsPrelude'HsPc'pp'item i = case i of
  B'HsPrelude'HsPcItem'Tokens ts -> b'HsPrelude'HsPc'pp'tokens ts
  B'HsPrelude'HsPcItem'Label l -> l
  B'HsPrelude'HsPcItem'Eoi -> "end of input"

b'HsPrelude'HsPc'pp'items :: (B'List B'HsPrelude'HsPcItem) -> (B'List (B'List B'Char)) -> (B'List (B'List B'Char))
b'HsPrelude'HsPc'pp'items xs acc = case xs of
  [] -> acc
  h : t -> b'HsPrelude'HsPc'pp'items t (b'HsPrelude'HsPc'sset'ins (b'HsPrelude'HsPc'pp'item h) acc)

b'HsPrelude'HsPc'pp'commas :: (B'List (B'List B'Char)) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'commas xs = case xs of
  [x] -> "or " ++ x
  x : y : t -> concat [x, ", ", b'HsPrelude'HsPc'pp'commas (y : t)]
  [] -> []

-- orList
b'HsPrelude'HsPc'pp'or :: (B'List (B'List B'Char)) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'or xs = case xs of
  [x] -> x
  [x, y] -> concat [x, " or ", y]
  x : y : z : t -> concat [x, ", ", b'HsPrelude'HsPc'pp'commas (y : z : t)]
  [] -> []

b'HsPrelude'HsPc'pp'msg :: B'String -> (B'List (B'List B'Char)) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'msg pre xs = case xs of
  [] -> []
  _ -> concat [pre, b'HsPrelude'HsPc'pp'or xs, "\n"]

b'HsPrelude'HsPc'pp'un :: (B'Maybe B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem)
b'HsPrelude'HsPc'pp'un u = case u of { Nothing -> []; Just i -> [i] }

b'HsPrelude'HsPc'pp'cmpword :: B'Cmp -> (B'List B'Char)
b'HsPrelude'HsPc'pp'cmpword o = case o of
  LT -> "less than "
  EQ -> "equal to "
  GT -> "greater than "

b'HsPrelude'HsPc'pp'fancy :: B'HsPrelude'HsPcFancy -> (B'List B'Char)
b'HsPrelude'HsPc'pp'fancy f = case f of
  B'HsPrelude'HsPcFancy'Fail m -> m
  B'HsPrelude'HsPcFancy'Indent o r a ->
    concat ["incorrect indentation (got ", b'HsPrelude'HsPc'pp'nat a, ", should be ", b'HsPrelude'HsPc'pp'cmpword o, b'HsPrelude'HsPc'pp'nat r, ")"]

b'HsPrelude'HsPc'pp'unlines :: (B'List B'HsPrelude'HsPcFancy) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'unlines xs = case xs of
  [] -> []
  h : t -> concat [b'HsPrelude'HsPc'pp'fancy h, "\n", b'HsPrelude'HsPc'pp'unlines t]

b'HsPrelude'HsPc'pp'trivial :: (B'Maybe B'HsPrelude'HsPcItem) -> (B'List B'HsPrelude'HsPcItem) -> (B'List B'Char)
b'HsPrelude'HsPc'pp'trivial u ps = case (u, ps) of
  (Nothing, []) -> "unknown parse error\n"
  (un, es) ->
    b'HsPrelude'HsPc'pp'msg "unexpected " (b'HsPrelude'HsPc'pp'items (b'HsPrelude'HsPc'pp'un un) [])
      ++ b'HsPrelude'HsPc'pp'msg "expecting " (b'HsPrelude'HsPc'pp'items es [])

-- parseErrorTextPretty
b'HsPrelude'HsPc'pp'text :: B'HsPrelude'HsPcError -> (B'List B'Char)
b'HsPrelude'HsPc'pp'text e = case e of
  B'HsPrelude'HsPcError'Trivial _ u ps -> b'HsPrelude'HsPc'pp'trivial u ps
  B'HsPrelude'HsPcError'Fancy _ [] -> "unknown fancy parse error\n"
  B'HsPrelude'HsPcError'Fancy _ xs -> b'HsPrelude'HsPc'pp'unlines xs

-- the pointer's length: the unexpected item's (tokens: their number), else 1
b'HsPrelude'HsPc'pp'elen :: B'HsPrelude'HsPcError -> B'Nat
b'HsPrelude'HsPc'pp'elen e = case e of
  B'HsPrelude'HsPcError'Trivial _ (Just (B'HsPrelude'HsPcItem'Tokens ts)) _ -> genericLength ts
  _ -> 1

b'HsPrelude'HsPc'pp'where :: (B'List B'Char) -> B'Nat -> B'Nat -> (B'List B'Char)
b'HsPrelude'HsPc'pp'where name l c =
  let lc = concat [b'HsPrelude'HsPc'pp'nat l, ":", b'HsPrelude'HsPc'pp'nat c]
  in if null name then lc else concat [name, ":", lc]

b'HsPrelude'HsPc'pp'at :: (B'List B'Char) -> B'HsPrelude'HsPcAt -> B'HsPrelude'HsPcError -> (B'List B'Char)
b'HsPrelude'HsPc'pp'at name (B'HsPrelude'HsPcAt l c pre post) e =
  let sline = b'HsPrelude'HsPc'pp'nonempty (b'HsPrelude'HsPc'pp'tabs (reverse pre ++ b'HsPrelude'HsPc'pp'line post) 0)
      rpshift = pc'nsub c 1
      slen = genericLength sline
      elen = b'HsPrelude'HsPc'pp'elen e
      plen = if rpshift + elen > slen then pc'nsub (1 + slen) rpshift else elen
      lnum = b'HsPrelude'HsPc'pp'nat l
      pad = replicate (1 + genericLength lnum) ' '
      rpad = if plen > 0 then genericReplicate rpshift ' ' else []
  in concat [ b'HsPrelude'HsPc'pp'where name l c, ":\n", pad, "|\n", lnum, " | ", sline, "\n", pad, "| ", rpad
            , genericReplicate plen '^', "\n", b'HsPrelude'HsPc'pp'text e ]

-- errorBundlePretty, for a bundle of one error (runParser's)
b'HsPrelude'HsPc'errorBundlePretty :: B'HsPrelude'HsPcBundle -> (B'List B'Char)
b'HsPrelude'HsPc'errorBundlePretty (B'HsPrelude'HsPcBundle e inp name) =
  b'HsPrelude'HsPc'pp'at name (b'HsPrelude'HsPc'pp'walk (b'HsPrelude'HsPc'err'off e) inp 1 1 []) e