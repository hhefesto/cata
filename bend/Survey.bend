import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X

# Survey: which bindings of hs-export's modules (tools/hs-export/FORMAT.md)
# fall in cata hs's first version, and why the others do not.  It
# translates nothing.  `survey OUT FILE.sexp...` appends to OUT, for every
# binding a user wrote, one line:
#
#   FILE  NAME  KIND  ok|no  WHY  INFO
#
# KIND is `fun` (a top-level binding) or `inst` (an instance's method); WHY
# lists, `;`-separated, what keeps the binding out of the first version
# (empty when it is ok), INFO what its translation will have to do but can
# (a list comprehension, an explicit comparison passed for Eq or Ord, a
# structural recursion, ...).  A module GHC rejected is one line, NAME
# `*module*`, WHY `ghc-error`.
#
# The first version (PLAN.md, "cata hs v1") takes:
#   - data types and records with no existential and no constraint;
#   - Int and Integer as Nat, only where nothing subtracts or negates;
#     Bool, Char, String, lists, Maybe, Either, tuples, Ordering, Float;
#   - Eq and Ord, passed as explicit comparisons; Show at base types;
#   - guards, where, let, case, if, lambdas, list comprehensions;
#   - recursion that visibly gets smaller: some parameter that every
#     recursive call passes a part of, taken apart by a pattern;
# and leaves out, each a reason in WHY:
#   - infinite lists and other laziness (enumFrom, iterate, repeat, cycle,
#     lazy patterns), partial functions (head, tail, fromJust, error, ...),
#     IO and every other monad, Read, Double, user classes;
#   - recursion that does not visibly get smaller, recursion through a
#     value (`map f` inside f), mutual recursion;
#   - any binding that calls one left out (WHY `calls:NAME`).
#
# Bend allows no mutual recursion and no call to a def below the caller,
# so every walk here is one def recursing on parts of its first parameter,
# its helpers above it.  Every def is prefixed `sv.`.

# Text ---------------------------------------------------------------------

# whether every char of s is below 128
def sv.ascii(+s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{c}, t}:
      Bool.and(U32.is_lt(c, 128), sv.ascii(t))

# the bytes x are the ASCII string s (ok: so far)
def sv.is.go(x: List<&2, U32>, s: String, ok: Bool) -> Bool:
  match x s ok:
    case _ _ False{}:
      False{}
    case Nil{} SNil{} True{}:
      True{}
    case b <> xt SCon{Chr{c}, st} True{}:
      sv.is.go(xt, st, U32.is_eq(b, c))
    case _ _ True{}:
      False{}

def sv.is.at(asc: Bool, +x: List<&2, U32>, s: String) -> Bool:
  match asc:
    case True{}:
      sv.is.go(x, s, True{})
    case False{}:
      S.eq(x, S.b(s))

# x is s's bytes: an ASCII s read beside them, a char a byte, any other
# made bytes (S.b at every call was a third of Spec's time: Spec's sp.is)
def sv.is(+x: List<&2, U32>, +s: String) -> Bool:
  sv.is.at(sv.ascii(s), x, s)

def sv.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def sv.cat3(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> List<&2, U32>:
  sv.cat(a, sv.cat(b, c))

def sv.strs(xs: List<String>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      S.b(h) <> sv.strs(t)

# whether a name starts with c
def sv.starts(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case h <> t:
      U32.is_eq(h, c)
    case Nil{}:
      False{}

# whether a name is GHC's own ($tc.., $trModule, $f.., $c..)
def sv.dollar(xs: List<&2, U32>) -> Bool:
  sv.starts(xs, 36)

# whether a name is a pattern synonym's builder ($bX): kept, as a def other
# modules call
def sv.isb(xs: List<&2, U32>) -> Bool:
  match xs:
    case h <> b <> t:
      Bool.and(U32.is_eq(h, 36), U32.is_eq(b, 98))
    case _:
      False{}

# a $-name the survey leaves out: GHC's (a dictionary, a worker), not an
# instance's method or a builder
def sv.dollar.out(+xs: List<&2, U32>) -> Bool:
  Bool.and(sv.dollar(xs), Bool.not(sv.isb(xs)))

# whether a name is an instance's method ($c..)
def sv.inst(xs: List<&2, U32>) -> Bool:
  match xs:
    case h <> c <> p <> +d <> t:
      Bool.and(Bool.and(U32.is_eq(h, 36), U32.is_eq(c, 99)), Bool.not(Bool.and(U32.is_eq(p, 112), Bool.and(U32.is_ge(d, 48), U32.is_le(d, 57)))))
    case h <> c <> t:
      Bool.and(U32.is_eq(h, 36), U32.is_eq(c, 99))
    case _:
      False{}

# Trees --------------------------------------------------------------------

# whether two trees are the same
def sv.sxeq.go(a: X.Sx, b: X.Sx) -> Bool:
  match a b:
    case X.SxAtom{x} X.SxAtom{y}:
      S.eq(x, y)
    case X.SxStr{x} X.SxStr{y}:
      S.eq(x, y)
    case X.SxNil{} X.SxNil{}:
      True{}
    case X.SxCons{h1, t1} X.SxCons{h2, t2}:
      Bool.and(sv.sxeq.go(h1, h2), sv.sxeq.go(t1, t2))
    case _ _:
      False{}

def sv.sxeq(+a: X.Sx, +b: X.Sx) -> Bool:
  sv.sxeq.go(a, b)

# a list tree's head atom, element i, string element i
def sv.hd(+x: X.Sx) -> List<&2, U32>:
  X.tsx.head(x)

def sv.at(+x: X.Sx, i: Nat) -> X.Sx:
  X.tsx.at(i, x)

def sv.str(+x: X.Sx, i: Nat) -> List<&2, U32>:
  X.tsx.str.of(X.tsx.at(i, x))

# whether the atom a occurs anywhere in x
def sv.has(x: X.Sx, +a: List<&2, U32>) -> Bool:
  match x:
    case X.SxAtom{s}:
      S.eq(s, a)
    case X.SxCons{h, t}:
      Bool.or(sv.has(h, a), sv.has(t, a))
    case _:
      False{}

def sv.vname.flat2.if(g: Bool, +x: X.Sx) -> List<&2, U32>:
  match g:
    case True{}:
      sv.str(x, 2n)
    case False{}:
      sv.str(x, 1n)

def sv.vname.flat2(+x: X.Sx) -> List<&2, U32>:
  sv.vname.flat2.if(sv.is(sv.hd(x), "g"), x)

def sv.vname.flat.if(g: Bool, l: Bool, +x: X.Sx) -> List<&2, U32>:
  match g l:
    case True{} _:
      sv.str(x, 2n)
    case False{} True{}:
      sv.str(x, 1n)
    case False{} False{}:
      sv.vname.flat2(sv.at(x, 1n))

# the name a variable tree stands for: (g M N K), (l N I), and the one
# inside (self X) or (bv X T)
def sv.name(+x: X.Sx) -> List<&2, U32>:
  sv.vname.flat.if(sv.is(sv.hd(x), "g"), sv.is(sv.hd(x), "l"), x)

# Tables -------------------------------------------------------------------

# What the first version knows of GHC's base: functions it maps to cata's
# prelude (okf), partial ones, lazy ones, IO; constructors; the classes'
# methods it maps at each kind of type (okm) and the ones out (subm); base
# types; classes.
type Tb is Data:
  Tb{okf: List<&2, List<&2, U32>>, part: List<&2, List<&2, U32>>, lazy: List<&2, List<&2, U32>>, io: List<&2, List<&2, U32>>, okc: List<&2, List<&2, U32>>, okm: List<&2, List<&2, U32>>, subm: List<&2, List<&2, U32>>, okt: List<&2, List<&2, U32>>, cls: List<&2, List<&2, U32>>}

def sv.tb() -> Tb:
  okf = sv.strs(["traverse_", "for_", "filterM", "zipWithM_", "map", "intersection", "intersectionWith", "restrictKeys", "withoutKeys", "unionWithKey", "unionsWith", "fromSet", "split", "filter", "foldr", "foldl", "foldl'", "++", "concat", "concatMap", "reverse", "zip", "zip3", "zipWith", "zipWith3", "unzip", "unzip3", "take", "drop", "splitAt", "takeWhile", "dropWhile", "dropWhileEnd", "span", "break", "lookup", "notElem", "replicate", "not", "&&", "||", "otherwise", "fst", "snd", "maybe", "fromMaybe", "isJust", "isNothing", "catMaybes", "mapMaybe", "listToMaybe", "maybeToList", "either", "lefts", "rights", "partitionEithers", "isDigit", "isAlpha", "isAlphaNum", "isSpace", "isUpper", "isLower", "isPunctuation", "isLetter", "isHexDigit", "isOctDigit", "isAscii", "isControl", "isPrint", "isSeparator", "toUpper", "toLower", "ord", "chr", "digitToInt", "intToDigit", "even", "odd", "gcd", "lcm", "^", "id", "const", "flip", ".", "$", "$!", "seq", "uncurry", "curry", "words", "unwords", "lines", "unlines", "all", "any", "and", "or", "sort", "sortBy", "sortOn", "insert", "insertBy", "nub", "nubBy", "group", "groupBy", "isPrefixOf", "isSuffixOf", "isInfixOf", "isSubsequenceOf", "stripPrefix", "intercalate", "intersperse", "partition", "transpose", "scanl", "scanr", "subsequences", "permutations", "tails", "inits", "delete", "deleteBy", "\\\\", "union", "unionBy", "intersect", "intersectBy", "elemIndex", "elemIndices", "findIndex", "findIndices", "find", "comparing", "on", "fromIntegral", "showString", "showParen", "shows", "showChar", "unsnoc", "uncons", "genericLength", "bool", "<$>", "<&>", "realToFrac", "subtract", "lookup", "zipWith3", "rightSection", "leftSection", "isLeft", "isRight", "fromLeft", "fromRight", "isAsciiUpper", "isAsciiLower", "mapAccumL", "mapAccumR", "zip4", "genericTake", "genericDrop", "genericReplicate", "genericSplitAt", "asTypeOf", "numerator", "denominator", "foldl1'", "scanl'", "gets", "modify", "modify'", "evalState", "execState", "runState", "mapM_", "forM_", "forM", "foldM", "when", "unless", "void", "=<<", "runExceptT", "empty", "singleton", "insertWith", "member", "notMember", "findWithDefault", "adjust", "toList", "toAscList", "assocs", "fromList", "fromAscList", "fromDistinctAscList", "fromListWith", "elems", "keys", "keysSet", "size", "null", "unionWith", "unions", "difference", "mapWithKey", "filterWithKey", "foldrWithKey", "absurd", "liftA2", "runIdentity", "subtract", "hash", "pack", "unpack", "encode", "toStrict", "fromStrict", "zipFrom", "zipR", "zipWithFrom", "zipWithR", "swap", "trace", "notElem", "liftM2", "viewl", "|>", "<|", "coerce", "showVia", "showListVia", "showSpace", "showCommaSpace", "showList__", "optional", "option", "<?>", "label", "satisfy", "string", "char", "single", "anySingle", "charLiteral", "decimal", "indentLevel", "incorrectIndent", "skipLineComment", "lexeme", "symbol", "between", "getOffset", "getSourcePos", "runParser", "errorBundlePretty", "unPos", "space1", "sourceLine", "sourceColumn", "sourceName", "takeWhileP", "takeWhile1P", "%", "runReaderT", "runReader", "local", "asks", "runWriterT", "runWriter", "writer"])
  part = sv.strs(["head", "tail", "init", "last", "!!", "fromJust", "error", "errorWithoutStackTrace", "undefined", "foldr1", "foldl1", "maximumBy", "minimumBy", "scanl1", "scanr1", "read", "assert", "absurd", "cycle1", "recSelError", "noMethodBindingError", "patError", "reads", "readHex", "readOct", "readDec", "readSigned", "lex"])
  lazy = sv.strs(["iterate", "iterate'", "repeat", "cycle", "until", "fix", "unfoldr"])
  io = sv.strs(["putStrLn", "putStr", "print", "getLine", "getContents", "interact", "readFile", "writeFile", "appendFile", "readLn", "sequence_", "replicateM", "replicateM_", "zipWithM", "forever", "getArgs", "hFlush", "hPutStrLn", "hPutStr", "hGetLine", "hClose", "hSetBuffering", "exitWith", "exitFailure", "exitSuccess", "ioError", "userError", "trace", "traceShow", "newIORef", "readIORef", "writeIORef", "modifyIORef", "lift", "liftM", "liftM2", "liftA2", "ap", "join", "guard", "msum", ">=>", "<=<", "<$", "$>", "getProgName", "hGetContents", "stdin", "stdout", "stderr", "runMainIO", "main", "readIO"])
  okc = sv.strs([":", "[]", "True", "False", "Just", "Nothing", "Left", "Right", "LT", "EQ", "GT", "Unit", "Tuple2", "Tuple3", "Tuple4", "(,)", "(,,)", "(,,,)", "()", "I#", "C#", "F#", "Fix", ":<", "EmptyL", "WriterT"])
  # methods as CLASS.NAME@KIND; KIND N: Int or Integer, F: Float, C: Char,
  # B: Bool, L: a list or String, M: Maybe, U: a type of the module,
  # V: a type variable, *: any
  okm = sv.strs(["Enum.enumFromTo@HsInt", "Foldable.maximum@L", "Foldable.minimum@L", "Foldable.foldr1@L", "Foldable.foldl1@L", "Eq.==@*", "Eq./=@*", "Ord.compare@*", "Ord.<@*", "Ord.<=@*", "Ord.>@*", "Ord.>=@*", "Ord.max@*", "Ord.min@*", "Num.+@N", "Num.*@N", "Num.fromInteger@N", "Num.abs@N", "Num.signum@N", "Num.+@F", "Num.-@F", "Num.*@F", "Num.negate@F", "Num.fromInteger@F", "Num.abs@F", "Integral.div@N", "Integral.mod@N", "Integral.quot@N", "Integral.rem@N", "Integral.divMod@N", "Integral.quotRem@N", "Integral.toInteger@N", "Fractional./@F", "Fractional.fromRational@F", "Floating.pi@F", "Floating.sqrt@F", "Enum.succ@N", "Enum.succ@C", "Enum.toEnum@C", "Enum.fromEnum@C", "Enum.toEnum@N", "Enum.fromEnum@N", "Enum.enumFromTo@N", "Enum.enumFromTo@C", "Enum.enumFromThenTo@N", "Enum.enumFromThenTo@C", "Enum.fromEnum@U", "Enum.toEnum@U", "Enum.succ@U", "Enum.enumFromTo@U", "Bounded.minBound@U", "Bounded.maxBound@U", "Show.show@N", "Show.show@B", "Show.show@C", "Show.show@L", "Show.show@U", "Show.show@F", "Show.showsPrec@U", "Show.showsPrec@Unit", "Show.show@Unit", "Show.showsPrec@Tuple2", "Show.show@Tuple2", "Show.showsPrec@Map", "Show.show@Map", "Show.showsPrec@Set", "Show.show@Set", "Show.showList@U", "Show.showsPrec@N", "Foldable.foldr@L", "Foldable.foldl@L", "Foldable.foldl'@L", "Foldable.sum@L", "Foldable.product@L", "Foldable.length@L", "Foldable.null@L", "Foldable.elem@L", "Foldable.foldMap@L", "Foldable.toList@L", "Foldable.foldr@M", "Foldable.length@M", "Foldable.null@M", "Foldable.elem@M", "Foldable.and@L", "Foldable.or@L", "Foldable.any@L", "Foldable.all@L", "Functor.fmap@L", "Functor.fmap@M", "Semigroup.<>@L", "Num.+@U", "Num.*@U", "Num.-@U", "Num.negate@U", "Num.fromInteger@U", "Num.abs@U", "Num.signum@U", "Fractional./@U", "Fractional.fromRational@U", "Semigroup.<>@U", "Monoid.mempty@U", "Monoid.mappend@U", "Functor.fmap@U", "Foldable.foldr@U", "Foldable.foldMap@U", "Foldable.length@U", "Foldable.sum@U", "Foldable.toList@U", "Foldable.elem@U", "Foldable.null@U", "Semigroup.<>@Ordering", "Monoid.mempty@Ordering", "Monoid.mempty@L", "Monoid.mconcat@L", "Monoid.mappend@L", "RealFrac.truncate@F", "RealFrac.round@F", "RealFrac.floor@F", "RealFrac.ceiling@F", "Traversable.mapM@L", "Traversable.traverse@L", "Traversable.sequence@L", "Traversable.sequenceA@L", "Recursive.project@Fix", "Recursive.project@Cofree", "Recursive.cata@Fix", "Recursive.cata@Cofree", "Corecursive.embed@Fix", "Corecursive.embed@Cofree", "Monad.>>=@M", "Monad.>>@M", "Monad.return@M", "Applicative.pure@M", "Monad.>>=@Either", "Monad.>>@Either", "Monad.return@Either", "Applicative.pure@Either", "Functor.fmap@Either", "Monad.>>=@StateT", "Monad.>>@StateT", "Monad.return@StateT", "Applicative.pure@StateT", "Functor.fmap@StateT", "Applicative.<*>@StateT", "MonadState.get@*", "MonadState.put@*", "Monad.>>=@ExceptT", "Monad.>>@ExceptT", "Monad.return@ExceptT", "Applicative.pure@ExceptT", "Functor.fmap@ExceptT", "Applicative.*>@ExceptT", "Applicative.*>@StateT", "Applicative.*>@M", "Applicative.*>@Either", "MonadError.throwError@*", "Semigroup.<>@Map", "Semigroup.<>@Set", "Semigroup.<>@IntMap", "Semigroup.<>@IntSet", "Num.+@HsInt", "Num.-@HsInt", "Num.*@HsInt", "Num.negate@HsInt", "Num.abs@HsInt", "Num.signum@HsInt", "Num.fromInteger@HsInt", "Integral.div@HsInt", "Integral.mod@HsInt", "Integral.quot@HsInt", "Integral.rem@HsInt", "Integral.toInteger@HsInt", "Enum.succ@HsInt", "Enum.pred@HsInt", "Enum.toEnum@HsInt", "Enum.fromEnum@HsInt", "Show.show@HsInt", "Num.+@HsInteger", "Num.-@HsInteger", "Num.*@HsInteger", "Num.negate@HsInteger", "Num.abs@HsInteger", "Num.signum@HsInteger", "Num.fromInteger@HsInteger", "Integral.div@HsInteger", "Integral.mod@HsInteger", "Integral.quot@HsInteger", "Integral.rem@HsInteger", "Integral.toInteger@HsInteger", "Enum.succ@HsInteger", "Enum.pred@HsInteger", "Enum.toEnum@HsInteger", "Enum.fromEnum@HsInteger", "Show.show@HsInteger", "Applicative.pure@Identity", "Functor.fmap@Identity", "Applicative.<*>@Identity", "Applicative.liftA2@Identity", "Monad.>>=@Identity", "Monad.>>@Identity", "Monad.return@Identity", "Applicative.liftA2@M", "Applicative.liftA2@Either", "Applicative.liftA2@StateT", "Applicative.liftA2@ExceptT", "Show.show@HsDigest", "Show.showsPrec@HsDigest", "Foldable.foldr@Set", "Foldable.foldl@Set", "Foldable.foldl'@Set", "Foldable.length@Set", "Foldable.null@Set", "Foldable.elem@Set", "Foldable.sum@Set", "Foldable.toList@Set", "Monoid.mempty@Set", "Monoid.mappend@Set", "Foldable.foldr@Map", "Foldable.foldl@Map", "Foldable.foldl'@Map", "Foldable.length@Map", "Foldable.null@Map", "Foldable.elem@Map", "Foldable.sum@Map", "Foldable.toList@Map", "Monoid.mempty@Map", "Monoid.mappend@Map", "Functor.fmap@Map", "Monoid.mappend@L", "Monoid.mempty@Unit", "Bifunctor.first@Either", "Bifunctor.second@Either", "Bifunctor.bimap@Either", "Bifunctor.first@Tuple2", "Bifunctor.second@Tuple2", "Bifunctor.bimap@Tuple2", "Applicative.<*>@M", "Applicative.<*>@Either", "Applicative.<*>@ExceptT", "Show.showsPrec@L", "Show.showsPrec@M", "Show.showsPrec@C", "Show.showsPrec@B", "Show.showsPrec@HsInt", "Show.show@M", "Show.showList@C", "Show.showList@L", "Monad.>>=@ParsecT", "Monad.>>@ParsecT", "Monad.return@ParsecT", "Applicative.pure@ParsecT", "Applicative.<*>@ParsecT", "Applicative.*>@ParsecT", "Applicative.<*@ParsecT", "Functor.fmap@ParsecT", "Functor.<$@ParsecT", "Alternative.<|>@ParsecT", "Alternative.<|>@M", "Alternative.empty@M", "Alternative.empty@ParsecT", "MonadFail.fail@ParsecT", "MonadParsec.try@Void", "MonadParsec.eof@Void", "MonadParsec.notFollowedBy@Void", "MonadParsec.hidden@Void", "MonadParsec.lookAhead@Void", "MonadParsec.label@Void", "Bounded.maxBound@HsInt", "Bounded.minBound@HsInt", "Num.+@HsRational", "Num.-@HsRational", "Num.*@HsRational", "Num.negate@HsRational", "Num.abs@HsRational", "Num.signum@HsRational", "Num.fromInteger@HsRational", "Fractional./@HsRational", "Show.show@HsRational", "Show.showsPrec@HsRational", "Monad.>>=@ReaderT", "Monad.>>@ReaderT", "Monad.return@ReaderT", "Applicative.pure@ReaderT", "Functor.fmap@ReaderT", "Applicative.<*>@ReaderT", "Applicative.*>@ReaderT", "Applicative.liftA2@ReaderT", "MonadReader.ask@*", "MonadReader.local@*", "MonadReader.reader@*", "MonadTrans.lift@ReaderT", "Applicative.pure@L", "Monad.return@L", "Monad.>>=@WriterT", "Monad.>>@WriterT", "Monad.return@WriterT", "Applicative.pure@WriterT", "Functor.fmap@WriterT", "Applicative.<*>@WriterT", "Applicative.*>@WriterT", "Applicative.liftA2@WriterT", "MonadTrans.lift@WriterT", "Monoid.mconcat@Set", "Monoid.mconcat@L"])
  # methods inside the first version's types but out of it
  subm = sv.strs(["Num.-@N", "Num.negate@N", "Enum.pred@N", "Enum.pred@C", "Enum.enumFrom@N", "Enum.enumFrom@C", "Enum.enumFrom@U", "Enum.enumFromThen@N", "Enum.enumFromThen@C"])
  # base types the first version maps (classes are judged as constraints)
  okt = sv.strs(["Int", "Integer", "Bool", "Char", "List", "String", "Float", "Maybe", "Either", "Ordering", "Unit", "Tuple2", "Tuple3", "Tuple4", "ShowS", "Natural", "FUN", "FilePath", "LiftedRep", "Many", "One", "Type", "TYPE", "Constraint", "CONSTRAINT", "RuntimeRep", "Levity", "BoxedRep", "Multiplicity", "Symbol", "Fix", "Cofree", "CofreeF", "Base", "State", "StateT", "Identity", "ExceptT", "Map", "Set", "IntMap", "IntSet", "Key", "Void", "HsInt", "HsInteger", "HsDigest", "Word8", "Seq", "ViewL", "ParsecT", "Parsec", "Pos", "SourcePos", "ParseErrorBundle", "Token", "Tokens", "HsRational", "ReaderT", "Reader", "WriterT", "Writer"])
  cls = sv.strs(["Eq", "Ord", "Show", "Num", "Integral", "Fractional", "Floating", "Real", "RealFrac", "RealFloat", "Enum", "Bounded", "Read", "Functor", "Applicative", "Monad", "MonadFail", "Foldable", "Traversable", "Semigroup", "Monoid", "Alternative", "MonadPlus", "IsString", "IsList", "HasField", "Typeable", "Generic", "Data", "Ix", "Bits", "FiniteBits"])
  Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}

def sv.okf(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      okf

def sv.part(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      part

def sv.lazy(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      lazy

def sv.io(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      io

def sv.okc(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      okc

def sv.okm(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      okm

def sv.subm(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      subm

def sv.okt(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      okt

def sv.cls(+t: Tb) -> List<&2, List<&2, U32>>:
  match t:
    case Tb{okf, part, lazy, io, okc, okm, subm, okt, cls}:
      cls

# Results ------------------------------------------------------------------

# A binding's findings: what keeps it out (why), what its translation must
# do (info), and the names of its own module it calls (calls).
type Rs is Data:
  Rs{why: List<&2, List<&2, U32>>, info: List<&2, List<&2, U32>>, calls: List<&2, List<&2, U32>>}

def sv.rs0() -> Rs:
  Rs{Nil{}, Nil{}, Nil{}}

def sv.put.if(seen: Bool, x: List<&2, U32>, xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match seen:
    case True{}:
      xs
    case False{}:
      x <> xs

# x in front of xs unless xs holds it already
def sv.put(+x: List<&2, U32>, +xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  sv.put.if(S.mem(x, xs), x, xs)

def sv.why(r: Rs, +w: List<&2, U32>) -> Rs:
  match r:
    case Rs{a, i, c}:
      Rs{sv.put(w, a), i, c}

def sv.info(r: Rs, +w: List<&2, U32>) -> Rs:
  match r:
    case Rs{a, i, c}:
      Rs{a, sv.put(w, i), c}

def sv.call(r: Rs, +n: List<&2, U32>) -> Rs:
  match r:
    case Rs{a, i, c}:
      Rs{a, i, sv.put(n, c)}

def sv.why.if(b: Bool, r: Rs, +w: List<&2, U32>) -> Rs:
  match b:
    case True{}:
      sv.why(r, w)
    case False{}:
      r

def sv.info.if(b: Bool, r: Rs, +w: List<&2, U32>) -> Rs:
  match b:
    case True{}:
      sv.info(r, w)
    case False{}:
      r

# What the modules of a package before this one gave (package mode): the
# package's modules so far, and the key M.NAME of each binding,
# constructor, type and synonym of theirs that is in.  Outside a package
# both are empty: a module stands alone.
type Imp is Data:
  Imp{home: List<&2, List<&2, U32>>, ok: List<&2, List<&2, U32>>}

def sv.imp0() -> Imp:
  Imp{Nil{}, Nil{}}

# The module being read: its name, the tables, its own types and classes
# the first version cannot take (bad), and what its package gave before it.
type Env is Data:
  Env{mod: List<&2, U32>, tb: Tb, bad: List<&2, List<&2, U32>>, imp: Imp}

def sv.mod(+e: Env) -> List<&2, U32>:
  match e:
    case Env{m, t, b, i}:
      m

def sv.tbl(+e: Env) -> Tb:
  match e:
    case Env{m, t, b, i}:
      t

def sv.bad(+e: Env) -> List<&2, List<&2, U32>>:
  match e:
    case Env{m, t, b, i}:
      b

def sv.home(+e: Env) -> List<&2, List<&2, U32>>:
  match e:
    case Env{m, t, b, Imp{h, o}}:
      h

def sv.imp.ok(+e: Env) -> List<&2, List<&2, U32>>:
  match e:
    case Env{m, t, b, Imp{h, o}}:
      o

# M.NAME
def sv.key(+m: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  sv.cat3(m, S.b("."), n)

# Names --------------------------------------------------------------------

def sv.base.io(io: Bool, +n: List<&2, U32>, r: Rs) -> Rs:
  match io:
    case True{}:
      sv.why(r, sv.cat(S.b("io:"), n))
    case False{}:
      sv.why(r, sv.cat(S.b("base:"), n))

def sv.base.lazy(lazy: Bool, +t: Tb, +n: List<&2, U32>, r: Rs) -> Rs:
  match lazy:
    case True{}:
      sv.why(r, sv.cat(S.b("lazy:"), n))
    case False{}:
      sv.base.io(S.mem(n, sv.io(t)), n, r)

# the partial functions cata writes as a failure value (PLAN.md, "Partial
# functions": an Either, prelude/HsPartial.bend): info, not out
def sv.pok() -> List<&2, List<&2, U32>>:
  sv.strs(["error", "errorWithoutStackTrace", "undefined", "!", "!!", "head", "tail", "last", "init", "fromJust", "maximumBy", "minimumBy", "foldr1", "foldl1"])

def sv.base.pok(ok: Bool, +n: List<&2, U32>, r: Rs) -> Rs:
  match ok:
    case True{}:
      sv.info(r, sv.cat(S.b("partial:"), n))
    case False{}:
      sv.why(r, sv.cat(S.b("partial:"), n))

def sv.base.part(part: Bool, +t: Tb, +n: List<&2, U32>, r: Rs) -> Rs:
  match part:
    case True{}:
      sv.base.pok(S.mem(n, sv.pok()), n, r)
    case False{}:
      sv.base.lazy(S.mem(n, sv.lazy(t)), t, n, r)

# a base function: the first of okf, part, lazy, io that holds it decides
def sv.base.fn(ok: Bool, +t: Tb, +n: List<&2, U32>, r: Rs) -> Rs:
  match ok:
    case True{}:
      r
    case False{}:
      sv.base.part(Bool.or(S.mem(n, sv.part(t)), sv.is(n, "!")), t, n, r)

def sv.own.if(var: Bool, dollar: Bool, +n: List<&2, U32>, r: Rs) -> Rs:
  match var dollar:
    case True{} False{}:
      sv.call(r, n)
    case _ _:
      r

# a name of this module: a call when it is a function
def sv.own(+kind: X.Sx, +n: List<&2, U32>, r: Rs) -> Rs:
  sv.own.if(sv.is(X.tsx.atom.of(kind), "var"), sv.dollar(n), n, r)

def sv.other.var(var: Bool, con: Bool, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  match var con:
    case True{} _:
      sv.base.fn(S.mem(n, sv.okf(sv.tbl(e))), sv.tbl(e), n, r)
    case False{} True{}:
      sv.why.if(Bool.not(S.mem(n, sv.okc(sv.tbl(e)))), r, sv.cat(S.b("con:"), n))
    case False{} False{}:
      r

def sv.other.k(+k: List<&2, U32>, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  sv.other.var(sv.is(k, "var"), sv.is(k, "con"), n, e, r)

# a name of another module, by its kind (a method is judged where it is
# applied to its type)
def sv.other(+kind: X.Sx, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  sv.other.k(X.tsx.atom.of(kind), n, e, r)

def sv.imported.if(ok: Bool, +key: List<&2, U32>, r: Rs) -> Rs:
  match ok:
    case True{}:
      r
    case False{}:
      sv.why(r, sv.cat(S.b("import:"), key))

def sv.imported.k(named: Bool, +kind: X.Sx, +m: List<&2, U32>, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  match named:
    case True{}:
      sv.imported.if(S.mem(sv.key(m, n), sv.imp.ok(e)), sv.key(m, n), r)
    case False{}:
      sv.other(kind, n, e, r)

# a binding, constructor or selector of an earlier module of the package:
# in when that module kept it
def sv.imported(+kind: X.Sx, +m: List<&2, U32>, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  +k = X.tsx.atom.of(kind)
  sv.imported.k(Bool.or(sv.is(k, "var"), Bool.or(sv.is(k, "con"), sv.is(k, "sel"))), kind, m, n, e, r)

def sv.global.if(own: Bool, home: Bool, +kind: X.Sx, +m: List<&2, U32>, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  match own home:
    case True{} _:
      sv.own(kind, n, r)
    case False{} True{}:
      sv.imported(kind, m, n, e, r)
    case False{} False{}:
      sv.other(kind, n, e, r)

# (g MOD NAME KIND)
def sv.global(+x: X.Sx, +e: Env, r: Rs) -> Rs:
  +m = sv.str(x, 1n)
  sv.global.if(S.eq(m, sv.mod(e)), S.mem(m, sv.home(e)), sv.at(x, 3n), m, sv.str(x, 2n), e, r)

# Types --------------------------------------------------------------------

def sv.kind.pick(i: Bool, f: Bool, c: Bool, b: Bool, l: Bool, m: Bool, n: List<&2, U32>) -> List<&2, U32>:
  match i f c b l m:
    case True{} _ _ _ _ _:
      S.b("N")
    case False{} True{} _ _ _ _:
      S.b("F")
    case False{} False{} True{} _ _ _:
      S.b("C")
    case False{} False{} False{} True{} _ _:
      S.b("B")
    case False{} False{} False{} False{} True{} _:
      S.b("L")
    case False{} False{} False{} False{} False{} True{}:
      S.b("M")
    case _ _ _ _ _ _:
      n

def sv.kind.base(+n: List<&2, U32>) -> List<&2, U32>:
  sv.kind.pick(Bool.or(sv.is(n, "Int"), Bool.or(sv.is(n, "Integer"), sv.is(n, "Natural"))), sv.is(n, "Float"), sv.is(n, "Char"), sv.is(n, "Bool"), Bool.or(sv.is(n, "List"), sv.is(n, "String")), sv.is(n, "Maybe"), n)

def sv.kind.tc(+n: List<&2, U32>, own: Bool) -> List<&2, U32>:
  match own:
    case True{}:
      S.b("U")
    case False{}:
      sv.kind.base(n)

def sv.kind.tv(tv: Bool, tc: Bool, +t: X.Sx, +e: Env) -> List<&2, U32>:
  match tv tc:
    case True{} _:
      S.b("V")
    case False{} True{}:
      sv.kind.tc(sv.str(t, 2n), S.eq(sv.str(t, 1n), sv.mod(e)))
    case False{} False{}:
      S.b("X")

# the kind of type a method is applied at (see Tb's okm)
def sv.kind(+t: X.Sx, +e: Env) -> List<&2, U32>:
  sv.kind.tv(sv.is(sv.hd(t), "tv"), sv.is(sv.hd(t), "tc"), t, e)

def sv.method.why.go(sub: Bool, lazy: Bool, +co: List<&2, U32>, +k: List<&2, U32>) -> List<&2, U32>:
  match sub lazy:
    case True{} _:
      S.b("int-sub")
    case False{} True{}:
      S.b("lazy:enumFrom")
    case False{} False{}:
      sv.cat3(S.b("partial:"), co, sv.cat(S.b("@"), k))

# why a method inside the first version's types is out of it
def sv.method.why(+co: List<&2, U32>, +k: List<&2, U32>) -> List<&2, U32>:
  sv.method.why.go(Bool.or(sv.is(co, "Num.-"), Bool.or(sv.is(co, "Num.negate"), sv.is(co, "Enum.pred"))), Bool.or(sv.is(co, "Enum.enumFrom"), sv.is(co, "Enum.enumFromThen")), co, k)

def sv.method.sub(sub: Bool, +co: List<&2, U32>, +k: List<&2, U32>, r: Rs) -> Rs:
  match sub:
    case True{}:
      sv.why(r, sv.method.why(co, k))
    case False{}:
      sv.why(r, sv.cat3(S.b("method:"), co, sv.cat(S.b("@"), k)))

def sv.method.ok(ok: Bool, +co: List<&2, U32>, +k: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  match ok:
    case True{}:
      sv.info.if(sv.is(k, "V"), r, S.b("compare-param"))
    case False{}:
      sv.method.sub(Bool.or(S.mem(sv.cat3(co, S.b("@"), k), sv.subm(sv.tbl(e))), S.mem(sv.cat(co, S.b("@*")), sv.subm(sv.tbl(e)))), co, k, r)

def sv.method.key(+co: List<&2, U32>, +k: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  sv.method.ok(Bool.or(S.mem(sv.cat3(co, S.b("@"), k), sv.okm(sv.tbl(e))), S.mem(sv.cat(co, S.b("@*")), sv.okm(sv.tbl(e)))), co, k, e, r)

def sv.method.own(own: Bool, +cls: List<&2, U32>, +op: List<&2, U32>, +ty: X.Sx, +e: Env, r: Rs) -> Rs:
  match own:
    case True{}:
      sv.why(r, sv.cat(S.b("user-class:"), cls))
    case False{}:
      sv.method.key(sv.cat3(cls, S.b("."), op), sv.kind(ty, e), e, r)

# the method OP of class C applied at TYPE; a class of this module is out
def sv.method(+cmod: List<&2, U32>, +cls: List<&2, U32>, +op: List<&2, U32>, +ty: X.Sx, +e: Env, r: Rs) -> Rs:
  sv.method.own(S.eq(cmod, sv.mod(e)), cls, op, ty, e, r)

def sv.tycon.why.io(io: Bool, +n: List<&2, U32>) -> List<&2, U32>:
  match io:
    case True{}:
      S.b("io")
    case False{}:
      sv.cat(S.b("type:"), n)

def sv.tycon.if(own: Bool, home: Bool, +m: List<&2, U32>, +n: List<&2, U32>, +e: Env, r: Rs) -> Rs:
  match own home:
    case True{} _:
      sv.why.if(S.mem(n, sv.bad(e)), r, sv.cat(S.b("type:"), n))
    case False{} True{}:
      sv.why.if(Bool.not(S.mem(sv.key(m, n), sv.imp.ok(e))), r, sv.cat(S.b("import:"), sv.key(m, n)))
    case False{} False{}:
      sv.why.if(Bool.not(Bool.or(S.mem(n, sv.okt(sv.tbl(e))), S.mem(n, sv.cls(sv.tbl(e))))), r, sv.tycon.why.io(sv.is(n, "IO"), n))

# (tc MOD NAME ARG...)
def sv.tycon(+x: X.Sx, +e: Env, r: Rs) -> Rs:
  +m = sv.str(x, 1n)
  sv.tycon.if(S.eq(m, sv.mod(e)), S.mem(m, sv.home(e)), m, sv.str(x, 2n), e, r)

def sv.ctx.if(eqord: Bool, +n: List<&2, U32>, r: Rs) -> Rs:
  match eqord:
    case True{}:
      sv.info(r, S.b("compare-param"))
    case False{}:
      sv.why(r, sv.cat(S.b("class:"), n))

# (tctx (tc MOD CLASS ...) T): Eq and Ord become explicit comparisons
def sv.ctx(+c: X.Sx, r: Rs) -> Rs:
  sv.ctx.if(Bool.or(sv.is(sv.str(c, 2n), "Eq"), sv.is(sv.str(c, 2n), "Ord")), sv.str(c, 2n), r)

# Recursion ------------------------------------------------------------------
#
# A recursive function is in the first version when one parameter shrinks at
# every recursive call: the call passes, at that parameter's place, a
# variable a pattern took out of that parameter (out of a constructor of
# it, at any depth, in the function's own clauses, or in a case on the
# parameter or on such a part).  Bend checks the same once that parameter
# is put first.  A recursive call with fewer arguments than the function
# takes, or the function used as a value, is recursion through a value.

# A local variable's place: the parameter j it is (sub False) or a part of
# (sub True).
type Vs is Data:
  Vs{id: Nat, sub: Bool, j: Nat}

# the number in (l NAME N)
def sv.lid(+x: X.Sx) -> Nat:
  X.tsx.nat(X.tsx.at(2n, x))

# a pattern node: a binder (bv ..), one that takes its value apart, other
type Pk is Data:
  PkBv{}
  PkApart{}
  PkOther{}

def sv.pk.if(bv: Bool, apart: Bool) -> Pk:
  match bv apart:
    case True{} _:
      PkBv{}
    case False{} True{}:
      PkApart{}
    case False{} False{}:
      PkOther{}

def sv.pk(+x: X.Sx) -> Pk:
  sv.pk.if(sv.is(sv.hd(x), "bv"), Bool.or(sv.is(sv.hd(x), "pcon"), Bool.or(sv.is(sv.hd(x), "ptuple"), sv.is(sv.hd(x), "plist"))))

# the variables a pattern binds, each the parameter j or a part of it
def sv.pv(x: X.Sx, open: Bool, k: Pk, +j: Nat, +sub: Bool, acc: List<&2, Vs>) -> List<&2, Vs>:
  match x open k:
    case X.SxCons{h, t} True{} PkBv{}:
      Vs{sv.lid(X.tsx.at(0n, t)), sub, j} <> acc
    case X.SxCons{h, t} True{} PkApart{}:
      sv.pv(t, False{}, PkOther{}, j, True{}, acc)
    case X.SxCons{+h, t} True{} PkOther{}:
      sv.pv(t, False{}, PkOther{}, j, sub, sv.pv(h, True{}, sv.pk(h), j, sub, acc))
    case X.SxCons{+h, t} False{} _:
      sv.pv(t, False{}, PkOther{}, j, sub, sv.pv(h, True{}, sv.pk(h), j, sub, acc))
    case _ _ _:
      acc

# a clause's patterns (P1 .. Pn), parameter j onwards
def sv.pats(ps: X.Sx, +j: Nat, acc: List<&2, Vs>) -> List<&2, Vs>:
  match ps:
    case X.SxCons{+h, t}:
      sv.pats(t, 1n+j, sv.pv(h, True{}, sv.pk(h), j, False{}, acc))
    case _:
      acc

# every clause's (match (P..) GRHSS)
def sv.clauses(ms: X.Sx, acc: List<&2, Vs>) -> List<&2, Vs>:
  match ms:
    case X.SxCons{+h, t}:
      sv.clauses(t, sv.pats(sv.at(h, 1n), 0n, acc))
    case _:
      acc

# whether xs's first holds variable i
def sv.vs.hit(+xs: List<&2, Vs>, +i: Nat) -> Bool:
  match xs:
    case Vs{k, s, j} <> t:
      Nat.is_eq(k, i)
    case Nil{}:
      False{}

def sv.vs.go(xs: List<&2, Vs>, +i: Nat, hit: Bool) -> Maybe<&2, Vs>:
  match xs hit:
    case h <> t True{}:
      Some{h}
    case h <> +t False{}:
      sv.vs.go(t, i, sv.vs.hit(t, i))
    case _ _:
      None{}

# the place of variable i, if a pattern gave it one
def sv.vs.find(+xs: List<&2, Vs>, +i: Nat) -> Maybe<&2, Vs>:
  sv.vs.go(xs, i, sv.vs.hit(xs, i))

# a case's clauses, each one pattern, as parts of parameter j
def sv.case.cls(ms: X.Sx, +j: Nat, +sub: Bool, acc: List<&2, Vs>) -> List<&2, Vs>:
  match ms:
    case X.SxCons{+h, t}:
      sv.case.cls(t, j, sub, sv.pv(sv.at(sv.at(h, 1n), 0n), True{}, sv.pk(sv.at(sv.at(h, 1n), 0n)), j, sub, acc))
    case _:
      acc

def sv.case.with(m: Maybe<&2, Vs>, +ms: X.Sx, acc: List<&2, Vs>) -> List<&2, Vs>:
  match m:
    case Some{Vs{i, sub, +j}}:
      sv.case.cls(ms, j, sub, acc)
    case None{}:
      acc

def sv.case.var(isvar: Bool, +s: X.Sx, +ms: X.Sx, +acc: List<&2, Vs>) -> List<&2, Vs>:
  match isvar:
    case True{}:
      sv.case.with(sv.vs.find(acc, sv.lid(s)), ms, acc)
    case False{}:
      acc

# (case S (matches .. (CLAUSE..))): a case on a parameter or a part of one
# makes its patterns' variables parts of that parameter
def sv.case.add(+x: X.Sx, +acc: List<&2, Vs>) -> List<&2, Vs>:
  sv.case.var(sv.is(sv.hd(sv.at(x, 1n)), "l"), sv.at(x, 1n), sv.at(sv.at(x, 2n), 4n), acc)

# every case of x, outermost first, adding to the places
def sv.cases(x: X.Sx, open: Bool, iscase: Bool, acc: List<&2, Vs>) -> List<&2, Vs>:
  match x open iscase:
    case X.SxCons{+h, +t} True{} True{}:
      sv.cases(t, False{}, False{}, sv.case.add(X.SxCons{h, t}, acc))
    case X.SxCons{+h, t} True{} False{}:
      sv.cases(t, False{}, False{}, sv.cases(h, True{}, sv.is(sv.hd(h), "case"), acc))
    case X.SxCons{+h, t} False{} _:
      sv.cases(t, False{}, False{}, sv.cases(h, True{}, sv.is(sv.hd(h), "case"), acc))
    case _ _ _:
      acc

# a node of the body: the function itself (esc: not called), an
# application not inside another's head (top), a wrapper inside a head
# (tyapp, evapp, cast), anything else
type Ck is Data:
  CkF{esc: Bool}
  CkApp{top: Bool}
  CkWrap{}
  CkOther{}

def sv.ck.if(f: Bool, app: Bool, wrap: Bool, sp: Bool) -> Ck:
  match f app wrap sp:
    case True{} _ _ _:
      CkF{Bool.not(sp)}
    case False{} True{} _ _:
      CkApp{Bool.not(sp)}
    case False{} False{} True{} True{}:
      CkWrap{}
    case _ _ _ _:
      CkOther{}

# x's kind; sp says whether x is in an application's head
def sv.ck(+x: X.Sx, +f: X.Sx, +g: X.Sx, sp: Bool) -> Ck:
  sv.ck.if(Bool.or(sv.sxeq(x, f), sv.sxeq(x, g)), sv.is(sv.hd(x), "app"), Bool.or(sv.is(sv.hd(x), "tyapp"), Bool.or(sv.is(sv.hd(x), "evapp"), sv.is(sv.hd(x), "cast"))), sp)

# an application's head and arguments: (app F A) is F's head with A last;
# tyapp, evapp (a dictionary) and cast add none
type Uk is Data:
  UkApp{}
  UkWrap{}
  UkStop{}

def sv.uk.if(app: Bool, wrap: Bool) -> Uk:
  match app wrap:
    case True{} _:
      UkApp{}
    case False{} True{}:
      UkWrap{}
    case False{} False{}:
      UkStop{}

def sv.uk(+x: X.Sx) -> Uk:
  sv.uk.if(sv.is(sv.hd(x), "app"), Bool.or(sv.is(sv.hd(x), "tyapp"), Bool.or(sv.is(sv.hd(x), "evapp"), sv.is(sv.hd(x), "cast"))))

def sv.unwind(x: X.Sx, k: Uk, args: List<&2, X.Sx>) -> X.Sx & List<&2, X.Sx>:
  match x k:
    case X.SxCons{h, X.SxCons{+fn, X.SxCons{ar, X.SxNil{}}}} UkApp{}:
      sv.unwind(fn, sv.uk(fn), ar <> args)
    case X.SxCons{h, X.SxCons{+e1, rest}} UkWrap{}:
      sv.unwind(e1, sv.uk(e1), args)
    case y _:
      (y, args)

def sv.dec.same(same: Bool, +j: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match same:
    case True{}:
      j <> acc
    case False{}:
      acc

def sv.dec.if(sub: Bool, +i: Nat, +j: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match sub:
    case True{}:
      sv.dec.same(Nat.is_eq(i, j), j, acc)
    case False{}:
      acc

def sv.dec.vs(m: Maybe<&2, Vs>, +i: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Some{Vs{v, sub, +j}}:
      sv.dec.if(sub, i, j, acc)
    case None{}:
      acc

def sv.dec.arg(isvar: Bool, +a: X.Sx, +i: Nat, +vs: List<&2, Vs>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match isvar:
    case True{}:
      sv.dec.vs(sv.vs.find(vs, sv.lid(a)), i, acc)
    case False{}:
      acc

# the places i where a call's argument i is a part of parameter i
def sv.dec(args: List<&2, X.Sx>, +i: Nat, +vs: List<&2, Vs>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match args:
    case +a <> t:
      sv.dec(t, 1n+i, vs, sv.dec.arg(sv.is(sv.hd(a), "l"), a, i, vs, acc))
    case Nil{}:
      acc

def sv.nat.mem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case h <> t:
      Bool.or(Nat.is_eq(h, x), sv.nat.mem(t, x))
    case Nil{}:
      False{}

def sv.inter.put(keep: Bool, +h: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}:
      h <> acc
    case False{}:
      acc

# the elements of xs also in ys
def sv.inter(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case +h <> t:
      sv.inter.put(sv.nat.mem(ys, h), h, sv.inter(t, ys))
    case Nil{}:
      Nil{}

# The recursive calls seen so far: how many, how many uses as a value, and
# the places every call so far shrinks (None before the first call).
type Cl is Data:
  Cl{n: Nat, esc: Nat, cand: Maybe<&2, List<&2, Nat>>}

def sv.cl.esc(esc: Bool, c: Cl) -> Cl:
  match esc c:
    case True{} Cl{n, e, k}:
      Cl{n, 1n+e, k}
    case False{} c2:
      c2

def sv.cl.cand(m: Maybe<&2, List<&2, Nat>>, +ps: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      Some{ps}
    case Some{xs}:
      Some{sv.inter(xs, ps)}

def sv.cl.add(full: Bool, +ps: List<&2, Nat>, c: Cl) -> Cl:
  match full c:
    case True{} Cl{n, e, k}:
      Cl{1n+n, e, sv.cl.cand(k, ps)}
    case False{} Cl{n, e, k}:
      Cl{n, 1n+e, k}

# f by itself, not an application's head: a call when f takes no
# parameters (a value that recurs: settle = .. >> settle), else a use as a
# value; in a head, the application has been counted
def sv.cl.ref(esc: Bool, arity: Nat, c: Cl) -> Cl:
  match esc arity:
    case True{} 0n:
      sv.cl.add(True{}, Nil{}, c)
    case False{} 0n:
      c
    case e 1n+a:
      sv.cl.esc(e, c)

# a call of f with its arguments; fewer than the arity is a use as a value
def sv.cl.got(hit: Bool, +args: List<&2, X.Sx>, +arity: Nat, +vs: List<&2, Vs>, c: Cl) -> Cl:
  match hit:
    case True{}:
      sv.cl.add(Nat.is_ge(List.length(&2, X.Sx, args), arity), sv.dec(args, 0n, vs, Nil{}), c)
    case False{}:
      c

# whether a head is f
def sv.cl.is(+hd: X.Sx, +f: X.Sx, +g: X.Sx) -> Bool:
  Bool.or(sv.sxeq(hd, f), sv.sxeq(hd, g))

def sv.cl.head(r: X.Sx & List<&2, X.Sx>, +f: X.Sx, +g: X.Sx, +arity: Nat, +vs: List<&2, Vs>, c: Cl) -> Cl:
  (hd, args) = r
  sv.cl.got(sv.cl.is(hd, f, g), args, arity, vs, c)

def sv.cl.call(top: Bool, +x: X.Sx, +f: X.Sx, +g: X.Sx, +arity: Nat, +vs: List<&2, Vs>, c: Cl) -> Cl:
  match top:
    case True{}:
      sv.cl.head(sv.unwind(x, sv.uk(x), Nil{}), f, g, arity, vs, c)
    case False{}:
      c

# every recursive call of f in x; g is f's global name when f is
# (self (g ..)): a function with a type signature calls itself by it
def sv.calls(x: X.Sx, open: Bool, k: Ck, +f: X.Sx, +g: X.Sx, +arity: Nat, +vs: List<&2, Vs>, c: Cl) -> Cl:
  match x open k:
    case X.SxCons{h, t} True{} CkF{esc}:
      sv.cl.ref(esc, arity, c)
    case X.SxCons{+h, X.SxCons{+fn, X.SxCons{+ar, X.SxNil{}}}} True{} CkApp{top}:
      c1 = sv.cl.call(top, X.SxCons{h, X.SxCons{fn, X.SxCons{ar, X.SxNil{}}}}, f, g, arity, vs, c)
      c2 = sv.calls(fn, True{}, sv.ck(fn, f, g, True{}), f, g, arity, vs, c1)
      sv.calls(ar, True{}, sv.ck(ar, f, g, False{}), f, g, arity, vs, c2)
    case X.SxCons{h, X.SxCons{+e1, rest}} True{} CkWrap{}:
      c1 = sv.calls(e1, True{}, sv.ck(e1, f, g, True{}), f, g, arity, vs, c)
      sv.calls(rest, False{}, CkOther{}, f, g, arity, vs, c1)
    case X.SxCons{+h, t} True{} _:
      sv.calls(t, False{}, CkOther{}, f, g, arity, vs, sv.calls(h, True{}, sv.ck(h, f, g, False{}), f, g, arity, vs, c))
    case X.SxCons{+h, t} False{} _:
      sv.calls(t, False{}, CkOther{}, f, g, arity, vs, sv.calls(h, True{}, sv.ck(h, f, g, False{}), f, g, arity, vs, c))
    case _ _ _:
      c

def sv.rec.cand(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case Some{xs}:
      Bool.not(List.is_empty(&2, Nat, xs))
    case None{}:
      True{}

def sv.rec.shrink(ok: Bool, +name: List<&2, U32>, r: Rs) -> Rs:
  match ok:
    case True{}:
      sv.info(r, S.b("structural"))
    case False{}:
      sv.info(r, sv.cat(S.b("nonstructural:"), name))

def sv.rec.verdict(c: Cl, +name: List<&2, U32>, r: Rs) -> Rs:
  match c:
    case Cl{0n, 0n, k}:
      r
    case Cl{n, 1n+e, k}:
      sv.why(r, sv.cat(S.b("rec-value:"), name))
    case Cl{n, 0n, k}:
      sv.rec.shrink(sv.rec.cand(k), name, r)

# the global inside (self (g ..)), else f itself
def sv.rec.global.if(self: Bool, +f: X.Sx) -> X.Sx:
  match self:
    case True{}:
      sv.at(f, 1n)
    case False{}:
      f

def sv.rec.global(+f: X.Sx) -> X.Sx:
  sv.rec.global.if(sv.is(sv.hd(f), "self"), f)

# (fun VAR TYPE SPAN (matches (ARGTY..) RES ORIGIN (CLAUSE..)) WRAP)
def sv.rec.fun(+f: X.Sx, +ms: X.Sx, r: Rs) -> Rs:
  vs = sv.cases(ms, True{}, False{}, sv.clauses(sv.at(ms, 4n), Nil{}))
  sv.rec.verdict(sv.calls(ms, True{}, CkOther{}, f, sv.rec.global(f), X.tsx.len(sv.at(ms, 1n)), vs, Cl{0n, 0n, None{}}), sv.name(f), r)

# One node --------------------------------------------------------------------

def sv.unsup(u: Bool, +x: X.Sx, r: Rs) -> Rs:
  match u:
    case True{}:
      sv.why(r, sv.cat3(S.b("unsupported:"), sv.str(x, 1n), sv.cat(S.b(":"), sv.str(x, 2n))))
    case False{}:
      r

# a do block (GHC expands it, FORMAT: expanded stmt) is judged by the
# >>= and >> it expands to, at their monad
def sv.stmt(ex: Bool, +x: X.Sx, r: Rs) -> Rs:
  r

# patterns and expressions the first version leaves out
def sv.here.rest(+h: List<&2, U32>, +x: X.Sx, r: Rs) -> Rs:
  r1 = sv.stmt(sv.is(h, "expanded"), x, r)
  r2 = sv.info.if(sv.is(h, "cast"), r1, S.b("coerce"))
  r3 = sv.unsup(sv.is(h, "unsupported"), x, r2)
  r4 = sv.why.if(sv.is(h, "wpfun"), r3, S.b("wpfun"))
  r5 = sv.why.if(sv.is(h, "pnplusk"), r4, S.b("n+k-pattern"))
  r6 = sv.why.if(sv.is(h, "pview"), r5, S.b("view-pattern"))
  sv.why.if(sv.is(h, "plazy"), r6, S.b("lazy-pattern"))

def sv.arith.if(lazy: Bool, r: Rs) -> Rs:
  match lazy:
    case True{}:
      sv.why(r, S.b("lazy:enumFrom"))
    case False{}:
      sv.info(r, S.b("range"))

def sv.arith(+k: List<&2, U32>, r: Rs) -> Rs:
  sv.arith.if(Bool.or(sv.is(k, "from"), sv.is(k, "fromthen")), r)

def sv.do.if(lc: Bool, +fl: List<&2, U32>, r: Rs) -> Rs:
  match lc:
    case True{}:
      sv.info(r, S.b("listcomp"))
    case False{}:
      sv.why(r, sv.cat(S.b("monad:"), fl))

def sv.do(+fl: List<&2, U32>, r: Rs) -> Rs:
  sv.do.if(sv.is(fl, "listcomp"), fl, r)

def sv.here.fun(fun: Bool, +h: List<&2, U32>, +x: X.Sx, r: Rs) -> Rs:
  match fun:
    case True{}:
      sv.rec.fun(sv.at(x, 1n), sv.at(x, 4n), r)
    case False{}:
      sv.here.rest(h, x, r)

def sv.here.arith(a: Bool, +h: List<&2, U32>, +x: X.Sx, r: Rs) -> Rs:
  match a:
    case True{}:
      sv.arith(sv.hd(sv.at(x, 2n)), r)
    case False{}:
      sv.here.fun(sv.is(h, "fun"), h, x, r)

def sv.here.do(d: Bool, +h: List<&2, U32>, +x: X.Sx, r: Rs) -> Rs:
  match d:
    case True{}:
      sv.do(X.tsx.atom.of(sv.at(x, 1n)), r)
    case False{}:
      sv.here.arith(sv.is(h, "arith"), h, x, r)

def sv.here.ctx(c: Bool, +h: List<&2, U32>, +x: X.Sx, r: Rs) -> Rs:
  match c:
    case True{}:
      sv.ctx(sv.at(x, 1n), r)
    case False{}:
      sv.here.do(sv.is(h, "do"), h, x, r)

def sv.here.tc(tc: Bool, +h: List<&2, U32>, +x: X.Sx, +e: Env, r: Rs) -> Rs:
  match tc:
    case True{}:
      sv.tycon(x, e, r)
    case False{}:
      sv.here.ctx(sv.is(h, "tctx"), h, x, r)

def sv.tyapp.if(m: Bool, +f: X.Sx, +ty: X.Sx, +e: Env, r: Rs) -> Rs:
  match m:
    case True{}:
      sv.method(sv.str(sv.at(f, 3n), 1n), sv.str(sv.at(f, 3n), 2n), sv.str(f, 2n), ty, e, r)
    case False{}:
      r

# (tyapp (g CM OP (method CM C)) TYPE): a method at its type
def sv.tyapp(+f: X.Sx, +ty: X.Sx, +e: Env, r: Rs) -> Rs:
  sv.tyapp.if(Bool.and(sv.is(sv.hd(f), "g"), sv.is(sv.hd(sv.at(f, 3n)), "method")), f, ty, e, r)

def sv.here.ty(ty: Bool, +h: List<&2, U32>, +x: X.Sx, +e: Env, r: Rs) -> Rs:
  match ty:
    case True{}:
      sv.tyapp(sv.at(x, 1n), sv.at(x, 2n), e, r)
    case False{}:
      sv.here.tc(sv.is(h, "tc"), h, x, e, r)

def sv.here.g(g: Bool, +h: List<&2, U32>, +x: X.Sx, +e: Env, r: Rs) -> Rs:
  match g:
    case True{}:
      sv.global(x, e, r)
    case False{}:
      sv.here.ty(sv.is(h, "tyapp"), h, x, e, r)

# an overloaded literal: its type
def sv.olit.ty(tc: Bool, +t: X.Sx, +e: Env, r: Rs) -> Rs:
  match tc:
    case True{}:
      sv.tycon(t, e, r)
    case False{}:
      r

def sv.olit(lit: Bool, +x: X.Sx, +e: Env, r: Rs) -> Rs:
  match lit:
    case True{}:
      sv.olit.ty(sv.is(sv.hd(sv.at(x, 2n)), "tc"), sv.at(x, 2n), e, r)
    case False{}:
      r

# what one list node says by itself (the walk visits its parts after)
def sv.here(+x: X.Sx, +e: Env, r: Rs) -> Rs:
  sv.here.g(sv.is(sv.hd(x), "g"), sv.hd(x), x, e, sv.olit(sv.is(sv.hd(x), "olit"), x, e, r))

# Every list node of x judged by sv.here.  `open` says whether x is a whole
# expression (True) or the rest of a list already opened (False), as in
# ToBend/Sexp.bend's printer.
# Which parts of a node the walk visits: all; none (a literal, whose
# witness, GHC's fromInteger or fromRational call, is GHC's, and evidence
# bindings); the first (evapp E D: a dictionary D is GHC's machinery); the
# second (evlam BINDER E, evlet BINDS E).
type Wk is Data:
  WkAll{}
  WkNone{}
  WkFirst{}
  WkSecond{}

def sv.wk.if(none: Bool, first: Bool, second: Bool) -> Wk:
  match none first second:
    case True{} _ _:
      WkNone{}
    case False{} True{} _:
      WkFirst{}
    case False{} False{} True{}:
      WkSecond{}
    case False{} False{} False{}:
      WkAll{}

def sv.wk(+x: X.Sx) -> Wk:
  sv.wk.if(Bool.or(Bool.or(sv.is(sv.hd(x), "olit"), sv.is(sv.hd(x), "pnlit")), Bool.or(sv.is(sv.hd(x), "evbinds"), sv.is(sv.hd(x), "evbind"))), sv.is(sv.hd(x), "evapp"), Bool.or(sv.is(sv.hd(x), "evlam"), sv.is(sv.hd(x), "evlet")))

def sv.walk(x: X.Sx, open: Bool, k: Wk, +e: Env, r: Rs) -> Rs:
  match x open k:
    case X.SxCons{+h, +t} True{} WkNone{}:
      sv.here(X.SxCons{h, t}, e, r)
    case X.SxCons{+h, X.SxCons{+a, rest}} True{} WkFirst{}:
      sv.walk(a, True{}, sv.wk(a), e, sv.here(X.SxCons{h, X.SxCons{a, rest}}, e, r))
    case X.SxCons{+h, X.SxCons{+a, X.SxCons{+b, rest}}} True{} WkSecond{}:
      sv.walk(b, True{}, sv.wk(b), e, sv.here(X.SxCons{h, X.SxCons{a, X.SxCons{b, rest}}}, e, r))
    case X.SxCons{+h, +t} True{} _:
      sv.walk(t, False{}, WkAll{}, e, sv.walk(h, True{}, sv.wk(h), e, sv.here(X.SxCons{h, t}, e, r)))
    case X.SxCons{+h, t} False{} _:
      sv.walk(t, False{}, WkAll{}, e, sv.walk(h, True{}, sv.wk(h), e, r))
    case _ _ _:
      r

# The module ----------------------------------------------------------------

# A binding: its name, kind (fun or inst) and findings.
type Fn is Data:
  Fn{name: List<&2, U32>, kind: List<&2, U32>, rs: Rs}

# a type of the module the first version cannot take: one with an
# existential or a constraint, or a part out of the first version
def sv.con.ex(+c: X.Sx) -> Bool:
  Bool.or(Nat.is_ne(X.tsx.nat(sv.at(sv.at(c, 4n), 1n)), 0n), Nat.is_ne(X.tsx.nat(sv.at(sv.at(c, 4n), 2n)), 0n))

def sv.cons.ex(cs: X.Sx) -> Bool:
  match cs:
    case X.SxCons{+h, t}:
      Bool.or(sv.con.ex(h), sv.cons.ex(t))
    case _:
      False{}

def sv.ty.bad.if(bad: Bool, +n: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match bad:
    case True{}:
      n <> acc
    case False{}:
      acc

def sv.ty.kind(+h: List<&2, U32>) -> Bool:
  Bool.or(sv.is(h, "data"), sv.is(h, "newtype"))

def sv.rs.why(r: Rs) -> List<&2, List<&2, U32>>:
  match r:
    case Rs{w, i, c}:
      w

def sv.ty.bad.of(dat: Bool, syn: Bool, cls: Bool, +x: X.Sx, +e: Env, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match dat syn cls:
    case True{} _ _:
      sv.ty.bad.if(Bool.or(sv.cons.ex(sv.at(x, 3n)), Bool.not(List.is_empty(&2, List<&2, U32>, sv.rs.why(sv.walk(sv.at(x, 3n), True{}, WkAll{}, e, sv.rs0()))))), sv.str(x, 1n), acc)
    case False{} True{} _:
      sv.ty.bad.if(Bool.not(List.is_empty(&2, List<&2, U32>, sv.rs.why(sv.walk(sv.at(x, 3n), True{}, WkAll{}, e, sv.rs0())))), sv.str(x, 1n), acc)
    case False{} False{} True{}:
      sv.str(x, 1n) <> acc
    case False{} False{} False{}:
      acc

# a data type, newtype or synonym: bad when its parts are; a class: bad
def sv.ty.bad(+x: X.Sx, +e: Env, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  sv.ty.bad.of(sv.ty.kind(sv.hd(x)), sv.is(sv.hd(x), "synonym"), sv.is(sv.hd(x), "class"), x, e, acc)

def sv.tys(xs: List<&2, X.Sx>, +e: Env, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      sv.tys(t, e, sv.ty.bad(h, e, acc))
    case Nil{}:
      acc

def sv.fn.keep(dollar: Bool, inst: Bool, gen: Bool) -> Bool:
  match dollar inst gen:
    case False{} _ _:
      True{}
    case True{} True{} False{}:
      True{}
    case _ _ _:
      False{}

def sv.fn.kind(inst: Bool) -> List<&2, U32>:
  match inst:
    case True{}:
      S.b("inst")
    case False{}:
      S.b("fun")

def sv.fn.group(many: Bool, r: Rs) -> Rs:
  match many:
    case True{}:
      sv.why(r, S.b("group"))
    case False{}:
      r

def sv.drop.if(same: Bool, h: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match same:
    case True{}:
      acc
    case False{}:
      h <> acc

# xs without n
def sv.drop(xs: List<&2, List<&2, U32>>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      sv.drop.if(S.eq(h, n), h, sv.drop(t, n))
    case Nil{}:
      Nil{}

# a binding's findings, its own name out of its calls (the walk saw it in
# the export list; its recursive calls are (self ..), not calls)
def sv.rs.self(r: Rs, +n: List<&2, U32>) -> Rs:
  match r:
    case Rs{w, i, c}:
      Rs{w, i, sv.drop(c, n)}

def sv.fn.if(keep: Bool, +n: List<&2, U32>, +r: Rs, acc: List<&2, Fn>) -> List<&2, Fn>:
  match keep:
    case True{}:
      Fn{n, sv.fn.kind(sv.inst(n)), sv.rs.self(r, n)} <> acc
    case False{}:
      acc

# each binder a binding exports, with the binding's findings
def sv.exports(xs: X.Sx, +r: Rs, +gen: Bool, acc: List<&2, Fn>) -> List<&2, Fn>:
  match xs:
    case X.SxCons{+h, t}:
      sv.exports(t, r, gen, sv.fn.if(Bool.and(sv.fn.keep(sv.dollar.out(sv.name(sv.at(h, 1n))), sv.inst(sv.name(sv.at(h, 1n))), gen), Bool.not(sv.is(X.tsx.atom.of(sv.at(sv.at(h, 1n), 3n)), "sel"))), sv.name(sv.at(h, 1n)), r, acc))
    case _:
      acc

def sv.top.abs(abs: Bool, +b: X.Sx, +e: Env, acc: List<&2, Fn>) -> List<&2, Fn>:
  match abs:
    case True{}:
      sv.exports(sv.at(b, 3n), sv.fn.group(Nat.is_gt(X.tsx.len(sv.at(b, 3n)), 1n), sv.walk(b, True{}, WkAll{}, e, sv.rs0())), sv.has(b, S.b("generated")), acc)
    case False{}:
      sv.fn.if(sv.fn.keep(sv.dollar.out(sv.name(sv.at(b, 1n))), sv.inst(sv.name(sv.at(b, 1n))), sv.has(b, S.b("generated"))), sv.name(sv.at(b, 1n)), sv.walk(b, True{}, WkAll{}, e, sv.rs0()), acc)

def sv.top.if(top: Bool, +x: X.Sx, +e: Env, acc: List<&2, Fn>) -> List<&2, Fn>:
  match top:
    case True{}:
      sv.top.abs(sv.is(sv.hd(sv.at(x, 1n)), "abs"), sv.at(x, 1n), e, acc)
    case False{}:
      acc

# every (top BIND) of the module
def sv.tops(xs: List<&2, X.Sx>, +e: Env, acc: List<&2, Fn>) -> List<&2, Fn>:
  match xs:
    case +h <> t:
      sv.tops(t, e, sv.top.if(sv.is(sv.hd(h), "top"), h, e, acc))
    case Nil{}:
      acc

# Calls between the module's bindings ----------------------------------------

def sv.fn.name(+f: Fn) -> List<&2, U32>:
  match f:
    case Fn{n, k, r}:
      n

def sv.fn.calls(+f: Fn) -> List<&2, List<&2, U32>>:
  match f:
    case Fn{n, k, Rs{w, i, c}}:
      c

def sv.fn.why(+f: Fn) -> List<&2, List<&2, U32>>:
  match f:
    case Fn{n, k, Rs{w, i, c}}:
      w

def sv.fns.hit(+fs: List<&2, Fn>, +n: List<&2, U32>) -> Bool:
  match fs:
    case h <> t:
      S.eq(sv.fn.name(h), n)
    case Nil{}:
      False{}

def sv.fns.go(fs: List<&2, Fn>, +n: List<&2, U32>, hit: Bool) -> List<&2, List<&2, U32>>:
  match fs hit:
    case h <> t True{}:
      sv.fn.calls(h)
    case h <> +t False{}:
      sv.fns.go(t, n, sv.fns.hit(t, n))
    case _ _:
      Nil{}

# the calls of the binding named n
def sv.fns.calls(+fs: List<&2, Fn>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  sv.fns.go(fs, n, sv.fns.hit(fs, n))

def sv.union(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      sv.put(h, sv.union(t, ys))
    case Nil{}:
      ys

# the calls of every name in ns, together
def sv.step(ns: List<&2, List<&2, U32>>, +fs: List<&2, Fn>) -> List<&2, List<&2, U32>>:
  match ns:
    case +h <> t:
      sv.union(sv.fns.calls(fs, h), sv.step(t, fs))
    case Nil{}:
      Nil{}

# every name reachable from ns in at most fuel steps (done once a step
# reaches nothing new)
def sv.reach(fuel: Nat, done: Bool, +ns: List<&2, List<&2, U32>>, +fs: List<&2, Fn>) -> List<&2, List<&2, U32>>:
  match fuel done:
    case 0n _:
      ns
    case 1n+p True{}:
      ns
    case 1n+p False{}:
      +n2 = sv.union(sv.step(ns, fs), ns)
      sv.reach(p, Nat.is_eq(List.length(&2, List<&2, U32>, n2), List.length(&2, List<&2, U32>, ns)), n2, fs)

def sv.missing.if(miss: Bool, +h: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match miss:
    case True{}:
      h <> acc
    case False{}:
      acc

# the names in ns that are bindings of the module (all) but not in ok
def sv.missing(ns: List<&2, List<&2, U32>>, +ok: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case +h <> t:
      sv.missing.if(Bool.and(S.mem(h, all), Bool.not(S.mem(h, ok))), h, sv.missing(t, ok, all))
    case Nil{}:
      Nil{}

def sv.names(fs: List<&2, Fn>) -> List<&2, List<&2, U32>>:
  match fs:
    case +h <> t:
      sv.fn.name(h) <> sv.names(t)
    case Nil{}:
      Nil{}

def sv.ok.if(ok: Bool, +n: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ok:
    case True{}:
      n <> acc
    case False{}:
      acc

# the names in ok whose binding has no finding of its own and calls only
# names in ok
def sv.ok.step(fs: List<&2, Fn>, +ok: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fs:
    case +h <> t:
      sv.ok.if(Bool.and(Bool.and(S.mem(sv.fn.name(h), ok), List.is_empty(&2, List<&2, U32>, sv.fn.why(h))), List.is_empty(&2, List<&2, U32>, sv.missing(sv.fn.calls(h), ok, all))), sv.fn.name(h), sv.ok.step(t, ok, all))
    case Nil{}:
      Nil{}

# the fixpoint of sv.ok.step from ok (done once a step takes nothing out)
def sv.ok.fix(fuel: Nat, done: Bool, +fs: List<&2, Fn>, +ok: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fuel done:
    case 0n _:
      ok
    case 1n+p True{}:
      ok
    case 1n+p False{}:
      +o2 = sv.ok.step(fs, ok, all)
      sv.ok.fix(p, Nat.is_eq(List.length(&2, List<&2, U32>, o2), List.length(&2, List<&2, U32>, ok)), fs, o2, all)

def sv.mutual.if(mut: Bool, r: Rs) -> Rs:
  match mut:
    case True{}:
      sv.info(r, S.b("mutual"))
    case False{}:
      r

# a binding that some binding it calls calls back is mutually recursive
def sv.mutuals(xs: List<&2, Fn>, +fs: List<&2, Fn>) -> List<&2, Fn>:
  match xs:
    case Fn{+n, k, Rs{w, i, c}} <> t:
      Fn{n, k, sv.mutual.if(S.mem(n, sv.reach(List.length(&2, Fn, fs), False{}, sv.fns.calls(fs, n), fs)), Rs{w, i, c})} <> sv.mutuals(t, fs)
    case Nil{}:
      Nil{}

# Output ----------------------------------------------------------------------

def sv.calls.why(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case h <> t:
      sv.cat(S.b("calls:"), h) <> sv.calls.why(t)
    case Nil{}:
      Nil{}

def sv.verdict(ok: Bool) -> List<&2, U32>:
  match ok:
    case True{}:
      S.b("ok")
    case False{}:
      S.b("no")

def sv.semi(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  S.join(List.reverse(&2, List<&2, U32>, xs), 59)

# FILE NAME KIND ok|no WHY INFO, and a newline
def sv.line(+file: List<&2, U32>, f: Fn, +ok: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match f:
    case Fn{+n, k, Rs{w, i, c}}:
      why = S.join(List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, w), sv.calls.why(sv.missing(c, ok, all))), 59)
      List.append(&2, U32, S.join(file <> n <> k <> sv.verdict(S.mem(n, ok)) <> why <> sv.semi(i) <> Nil{}, 9), 10 <> Nil{})

def sv.lines(xs: List<&2, Fn>, +file: List<&2, U32>, +ok: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case h <> t:
      List.append(&2, U32, sv.line(file, h, ok, all), sv.lines(t, file, ok, all))
    case Nil{}:
      Nil{}

# The driver ------------------------------------------------------------------

def sv.err.hit(+xs: List<&2, X.Sx>) -> Bool:
  match xs:
    case h <> t:
      sv.is(sv.hd(h), "error")
    case Nil{}:
      False{}

# whether GHC rejected the module (an (error ..) line)
def sv.err(xs: List<&2, X.Sx>) -> Bool:
  match xs:
    case +h <> t:
      Bool.or(sv.is(sv.hd(h), "error"), sv.err(t))
    case Nil{}:
      False{}

def sv.modname.hit(+xs: List<&2, X.Sx>) -> Bool:
  match xs:
    case h <> t:
      sv.is(sv.hd(h), "module")
    case Nil{}:
      False{}

def sv.modname.go(xs: List<&2, X.Sx>, hit: Bool) -> List<&2, U32>:
  match xs hit:
    case h <> t True{}:
      sv.str(h, 1n)
    case h <> +t False{}:
      sv.modname.go(t, sv.modname.hit(t))
    case _ _:
      Nil{}

# NAME in (module NAME (IMPORT..))
def sv.modname(+xs: List<&2, X.Sx>) -> List<&2, U32>:
  sv.modname.go(xs, sv.modname.hit(xs))

# Package mode ---------------------------------------------------------------

# M.N for each N of ns, onto acc
def sv.keys(+m: List<&2, U32>, ns: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case h <> t:
      sv.keys(m, t, sv.key(m, h) <> acc)
    case Nil{}:
      acc

# the names of a constructor's fields: (FIELD...), each a string
def sv.field.names(fs: X.Sx, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fs:
    case X.SxCons{X.SxStr{f}, t}:
      sv.field.names(t, f <> acc)
    case X.SxCons{f, t}:
      sv.field.names(t, acc)
    case _:
      acc

# the names of constructors and their fields: ((con NAME (FIELD...) ...)...)
def sv.con.names(cs: X.Sx, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case X.SxCons{+c, t}:
      sv.con.names(t, sv.str(c, 1n) <> sv.field.names(sv.at(c, 2n), acc))
    case _:
      acc

def sv.ty.names.in(out: Bool, isdata: Bool, +x: X.Sx, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match out isdata:
    case True{} _:
      acc
    case False{} True{}:
      sv.str(x, 1n) <> sv.con.names(sv.at(x, 3n), acc)
    case False{} False{}:
      sv.str(x, 1n) <> acc

def sv.ty.names.if(isty: Bool, isdata: Bool, +x: X.Sx, +bad: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match isty:
    case True{}:
      sv.ty.names.in(S.mem(sv.str(x, 1n), bad), isdata, x, acc)
    case False{}:
      acc

# the module's types, synonyms, constructors and fields that are in (a
# type not in bad), onto acc
def sv.ty.names(xs: List<&2, X.Sx>, +bad: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      +hd = sv.hd(h)
      +dat = Bool.or(sv.is(hd, "data"), sv.is(hd, "newtype"))
      sv.ty.names(t, bad, sv.ty.names.if(Bool.or(dat, sv.is(hd, "synonym")), dat, h, bad, acc))
    case Nil{}:
      acc

# a module's names, as keys, added to what the package gave
def sv.imp.add(i: Imp, +m: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> Imp:
  match i:
    case Imp{h, o}:
      Imp{m <> h, sv.keys(m, ns, o)}

# A module's lines, and what the package has after it
type Sv is Data:
  Sv{lines: List<&2, U32>, imp: Imp}

def sv.sv.lines(s: Sv) -> List<&2, U32>:
  match s:
    case Sv{l, i}:
      l

def sv.sv.imp(s: Sv) -> Imp:
  match s:
    case Sv{l, i}:
      i

def sv.module.both(+file: List<&2, U32>, +xs: List<&2, X.Sx>, +tb: Tb, +imp: Imp) -> Sv:
  +m = sv.modname(xs)
  +bad = sv.tys(xs, Env{m, tb, Nil{}, imp}, Nil{})
  +fs0 = sv.tops(xs, Env{m, tb, bad, imp}, Nil{})
  fs = sv.mutuals(List.reverse(&2, Fn, fs0), fs0)
  +all = sv.names(fs0)
  +ok = sv.ok.fix(1n+List.length(&2, Fn, fs0), False{}, fs0, all, all)
  Sv{sv.lines(fs, file, ok, all), sv.imp.add(imp, m, List.append(&2, List<&2, U32>, ok, sv.ty.names(xs, bad, Nil{})))}

def sv.module.ok(+file: List<&2, U32>, +xs: List<&2, X.Sx>, +tb: Tb) -> List<&2, U32>:
  sv.sv.lines(sv.module.both(file, xs, tb, sv.imp0()))

def sv.module.if(err: Bool, +file: List<&2, U32>, +xs: List<&2, X.Sx>, +tb: Tb, +imp: Imp) -> Sv:
  match err:
    case True{}:
      Sv{List.append(&2, U32, S.join(file <> S.b("*module*") <> S.b("module") <> S.b("no") <> S.b("ghc-error") <> Nil{} <> Nil{}, 9), 9 <> 10 <> Nil{}), sv.imp.add(imp, sv.modname(xs), Nil{})}
    case False{}:
      sv.module.both(file, xs, tb, imp)

# a module's lines, from its export's bytes, and what its package has after
# it (imp: what the package had before; sv.imp0() for a module alone)
def sv.module(+file: List<&2, U32>, bytes: List<&2, U32>, +tb: Tb, +imp: Imp) -> Sv:
  +xs = X.tsx.read(bytes)
  sv.module.if(sv.err(xs), file, xs, tb, imp)

# a module's package: what the modules before it gave, in package mode
def sv.next(pkg: Bool, +s: Sv) -> Imp:
  match pkg:
    case True{}:
      sv.sv.imp(s)
    case False{}:
      sv.imp0()

def sv.run(xs: List<String>, +out: String, +tb: Tb, +pkg: Bool, +imp: Imp) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +s : Sv <- IO.pure(Sv, sv.module(S.b(f), bytes, tb, imp))
        S.add(out, sv.sv.lines(s))
        sv.run(t, out, tb, pkg, sv.next(pkg, s))

# `survey OUT FILE...` judges each module alone; `survey --package OUT
# FILE...` reads the files as one package's modules in dependency order
# (hs-export --package's modules.txt), each seeing what the ones before it
# have in
def sv.main.go(pkg: Bool, args: List<String>) -> IO(Unit):
  match args:
    case out <> files:
      sv.run(files, out, sv.tb(), pkg, sv.imp0())
    case Nil{}:
      IO.print("usage: survey [--package] OUT FILE.sexp...")

def sv.main.pkg(pkg: Bool, a: String, rest: List<String>) -> IO(Unit):
  match pkg:
    case True{}:
      sv.main.go(True{}, rest)
    case False{}:
      sv.main.go(False{}, a <> rest)

def sv.main(args: List<String>) -> IO(Unit):
  match args:
    case +a <> rest:
      sv.main.pkg(S.eq(S.b(a), S.b("--package")), a, rest)
    case Nil{}:
      sv.main.go(False{}, Nil{})

def main() -> IO(Unit):
  do IO<Unit>:
    # IO.args leads with the program as invoked
    argv : List<String> <- IO.args()
    sv.main(List.tail(&1, String, argv))
