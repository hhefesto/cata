# cata

Checked Bend 2 by fixed rules: Haskell, Agda and specs in, Bend out. No
model takes part; a module the rules cannot translate is ledgered with its
reason. PLAN.md has the decisions, the steps and what has been measured.

## Parts

- `tools/hs-export` (Haskell, GHC 9.10.3's API): `hs-export OUT.sexp
  FILE.hs` type-checks one module and writes its typechecked syntax, every
  binder's type and every instance GHC chose, as S-expressions
  (`tools/hs-export/FORMAT.md`). It decides nothing.
- `bend/Spec.bend`: `spec OUTDIR FILE.sexp...` (a package's modules, in
  order) writes them again in the same format with each pattern synonym
  replaced by the pattern its matcher matches (or its builder), each view
  pattern whose function is known (a constructor, a projection, a function
  by cases that is Just at one constructor, Recursive's project and
  Corecursive's embed at Fix and Cofree, compositions of them, through the
  package's instances) as the plain pattern it is, and each call of a def
  that takes dictionaries, or of a method at an instance the package wrote,
  at types with no variable left, as a call of a copy at those types
  (`NAME__TYPES`, written into the calling module). It writes every type
  argument with the package's synonyms expanded and type families applied
  (`cata` at telomare's `Term3` is `cata` at `Cofree Term3F LocTag`), and
  each as-pattern `x@p` of a clause as `p`, its wildcards named and each
  use of `x` the term `p` builds (Bend matches a parameter and hands out
  its fields, not the whole as well). Survey, fold and law read its
  output.
- `bend/Survey.bend`: `survey OUT FILE.sexp...` judges every binding of
  the exports against cata hs's first version and says why each one out is
  out.
- `bend/Fold.bend`: `fold OUT FILE.sexp...` folds the bindings in that
  version into Bend, keeps what `bend --check-only` accepts (a gate that
  takes out a failing def and whatever uses it), and ledgers the rest with
  its reason (`OUT/ledger.tsv`).
- `bend/Law.bend`: `law OUT FILE.sexp...` is the fold plus example laws:
  it lists small inputs by each def's Haskell type, has GHC's interpreter
  run the original function on them (`OUT/NAME.ghci`, `OUT/NAME.ghc`), and
  writes each answer as a law, `def f.exK() -> {f(..) == v : R}: {==}`. A
  def whose law fails is out. The ledger says `ok-law` (the def checks and
  its laws hold), `ok-check` (it checks, no law, and why), `ok-type` or
  `out`. `GHC` names the ghc (`.#ghc`), `BEND` the bend.
- Shared with agda2bend: its Bend syntax tree, printer and S-expression
  reader (`ToBend/`) and `Sys.bend`, as `bend/a2b`.

## A package (several modules that import each other)

`hs-export --package OUTDIR ARGS` exports a package's modules at once and
lists them in dependency order in `OUTDIR/modules.txt`; `survey`, `fold`
and `law` take `--package` before OUT and read the files in that order,
each module seeing what the ones before it kept (their defs, constructors,
types and synonyms, by `M.NAME`), and importing their files as
`import ./M_N.bend as M_N`. Telomare master's library, for instance:

    nix build .#hs-export .#law .#ghc-telomare
    # ARGS: -iSRC, -XHaskell2010, -package-db GHCT/lib/ghc-9.10.3/lib/package.conf.d,
    # a line --, then src/Telomare/**/*.hs
    hs-export --package export ARGS
    GHC="GHCT/bin/ghc -iSRC -XHaskell2010 -fobject-code -outputdir OBJ" \
      law --package OUT $(cat export/modules.txt)

## Recursion schemes

`Fix f`, `Cofree f a` and `CofreeF f a b` (data-fix, free) become
`HsPrelude.Fix<F>`, `HsPrelude.Cofree<F, A>` and `HsPrelude.CofreeF<F, A,
B>`, written next to the modules as `OUT/HsPrelude.bend`, with the functor
as a type function: `Fix (PatternF t)` is `HsPrelude.Fix<(r_ => PatternF<T,
r_>)>`. `Fix`, both `:<` and `unFix` are their constructors and field;
recursion-schemes' `project` and `embed` at them are HsPrelude's defs or
constructors; `Base t a` is reduced. For each data type with a Functor
instance in its module (its last variable the recursive one), cata writes
`G.cata` and `G.cata.cofree` (the ledger's `ok-gen`): `cata` at `Fix G` and
at `Cofree G w`, as nested matches through the fields (a Maybe, a pair, or
another, flat functor of the package such as `StuckExprB (BasicExprF f)`),
which Bend sees shrink.

Two catas are written instead as a def of their own at the call, `D.cH`
in the def `D` (H a hash of the call's functor, types and algebra), the
ledger's `ok-gen`: one whose algebra calls back `D` (they are a group,
one def with fuel once merged, and `G.cata`'s template argument would hold
the fuel, which Bend refuses: `freeVarsDeep = cata alg`, whose `alg` calls
`patternRefs`, whose own cata's algebra calls `freeVarsDeep`), and one at a
functor with a list of its recursive variable (`[(Pattern, r)]`), which has
no `G.cata`, since Bend sees no list shrink. `D.cH` matches the value at
`Fix` or `Cofree` and its layer at the functor's constructors, and applies
the algebra to the layer; a recursive field is a call of `D.cH`, a list,
`Maybe`, pair or other functor of them a call of a def `D.cH.hP` mapping
it (P its path: constructor, field, part). They call each other, and so
are a group with fuel (see below), with `D`'s when it has one.

A layer of a monad's actions is a layer of functions (a cata at Reader or
State hands its algebra one, and `sequence` takes one), and Bend's Data
holds no function. So each of the package's types with type variables has
a twin, `D.fn`, when its fields allow one (each of the last variable, or of
another of the package's types at it): the last variable a Type and the
twin a Type, its constructors `D.fn.C`. The fold writes the twin wherever a
type's last argument is a function (or a twin), in types, patterns and
terms; `CofreeF f a b` at such a b is `HsPrelude.CofreeF.fn`, and `cata`
at such a result `G.cata.fn` or `G.cata.cofree.fn`, the same nested matches
building the twin's layer. A twin's functions are used once (Bend's Type
is not copied).

## Recursion Bend refuses: fuel

Bend takes a recursive call only when an argument shrinks, and no mutual
recursion; telomare's bend branch writes every other recursion with a Nat
fuel (Desugar.bend's `go(+fuel, scope, n: ON) -> OV`, `fuel()` 2^32 - 1),
and so does cata, never with `@unsafe`:

- A def whose self-call Bend refuses ("a decreasing self-call", read by
  the gate) becomes `f.fu`, a `Nat` after its type and template parameters,
  one less at each self-call, and `f` calls it from
  `U32.to_nat(4294967295)`, a depth no run reaches. At 0 it answers a
  default of its type: Base's (`0n`, `False{}`, `[]`, `None{}`, ...),
  HsPrelude's (HsInt 0, the empty Map and Set), a pair's, an Either's,
  Fix's and Cofree's from their parts', and a data type's, of the module or
  of one before it in the package: a constructor with no fields first, then
  one whose fields do not name the type, then any, its fields' defaults in
  turn. A type with none to hand (a type variable) leaves the def out.
  The default is a choice, kept (11-23): where h never stops, F's def
  answers it, more defined than h, so the adjunction (`adj/`, section 7)
  is proved for the programs that stop within the fuel, and refuted for
  one that never stops; a failure value instead would put every fuelled
  def and its callers in an Either.
- Defs that call each other are one def, `HEAD.mu(fuel_, in_)`, as the
  bend branch's mutual walks are: `HEAD.mu.In` has a constructor for each
  member holding its arguments, and the answer is theirs when they share
  it, else `HEAD.mu.Out`'s constructor for the member (`HEAD.mu.outK`
  takes it out). Each member is a call of `HEAD.mu` at its constructor.
  Members that lead with the same template parameters and pass them on
  unchanged at every call of a member (wordsWhen's `~p: Char -> Bool`,
  which the defs lifted out of it take too) keep them as `HEAD.mu`'s own,
  in front of the fuel: Bend takes such a cycle only as one def (a
  template calls only templates declared above it). A type parameter
  among them (`~A: Data`) is `HEAD.mu.In`'s too, when the members share
  their answer. A group whose members take other type or template
  parameters, or do not fold whole, is left as it was. A member whose answer is a function (written
  point-free, `freeD = cata alg`) takes its arguments as parameters of
  its own in the group (`HEAD.mu.Out`'s fields are data, and a function
  is not): its body is applied to them, its calls in the group are given
  the arguments they are applied to (else eta-expanded), and outside the
  group it is the lambda again.

The survey no longer puts a def out for either. Still out (`rec-value`):
recursion through a function value (`map f xs` inside `f`), as Bend's
templates take only closed arguments and the fuel is not one. The
specialiser writes `f $ x` as `f x` and `(f . g) x` as `f (g x)`, so a
call through them is a call.

## Known function arguments

A call of a package def at a function parameter whose argument is known
(a def, a partial application, a section, a lambda: anything but a local
variable) is a call of the def's copy `NAME__fHASH`, with the argument in
the parameter's place (Spec). The argument's free locals become the copy's
first parameters (`fv_0`, `fv_1`, ..), so a recursive call with the same
argument inside the copy is a call of the copy: in `sumT (N ts) = sum
(mapT sumT ts)`, `mapT__f..` calls `sumT`, and the two are one `.mu`.
Bend calls a closure at most once and takes a template only closed; a
function the def runs again (`twice f x = f (f x)`) is then plain code.
The call must be at closed types, and the def's patterns at the
parameter variables or wildcards. Not copied: a def's own self-calls
(`go (f . (x :)) xs`, whose argument grows) and, inside a copy, the def
at another argument. A dictionary local in the argument stays as it is:
the fold reads a method at its type. A local function in the argument (a
let's or a where's, nonrecursive, with parameters) is its lambda there,
an applied one reduced, so that the copy's parameters are its free locals
and not a closure over them: in Resolve's `pruneBindings`, `until (\s ->
expand s == s) expand seed` with `expand r = r <> fold (restrictKeys bmap
r)` is a call of until's copy at bmap, a Map. The copy then takes no
template for it, so a recursion through the copy (freeVarsDeep's, through
`foldMap (\(p, body) -> patternRefs p <> body)`) is a group the fold
writes with fuel. A call of a def's dictionary copy is the def's call at
the copy's types, so a def with a class is copied at a known argument
too, when the argument names a local or the def the call is in (else the
dictionary copy takes it as a template, closed).

Base's `foldr`, `foldl`, `foldl'` and `concatMap` at a list are cata's model's
(`prelude/Cata/Base.hs`, base's definitions, the list first in foldl's
loop so that Bend sees it shrink), exported with the package before
`Cata/Parsec.hs`: a call of one is a call of the model's def at the types
after the list (`sp.pc.btab`), so it is copied like the package's own. A
lambda over a pattern's variable (telomare's `parseApplied`: `foldl (\a b
-> x :< embedL (AppF a b)) f args`), which Bend refuses as a template (a
closure), is then a first-order def with the variable its parameter. A
package without the model keeps base's, the prelude's. In the copy, `(f .
g) x y` and `(op y) x z` (a composition or a section in the parameter's
place, applied to more than its one argument) are `f (g x) y` and `op x
y z`. A local's recursive reference (`self (l ..)`, a `where go` calling
itself) is a local's, so its lifting passes the def's type parameters
once.

## Monads

GHC hands a do block over as its `>>=` and `>>`, and cata writes those at
the monad they are at. At `Maybe` and `Either e`: Base's `Maybe.bind` or
the prelude's `hs.either.bind`, with the rest of the block as a closure;
`return`/`pure`, `fmap`/`<$>`, `maybe`, `either` and `fromMaybe` too. At
`State s` (`StateT s Identity`, lazy or strict): a function of the state to
a result and the next state, `S -> A & S` (an `&1` pair, so the result may
be a function, as at `<*>`), with the prelude's `hs.state.*`: `>>=`, `>>`,
`pure`, `fmap`, `<*>`, mtl's `get`, `put`, `modify`, `modify'` and `gets`,
and `evalState`, `execState` and `runState`. At `ExceptT e (State s)`
(`StateT s Identity` too): ExceptT's newtype, `m (Either e a)`, so a State
whose result is an Either, `S -> Either E A & S`, with the prelude's
`hs.exs.*` (`>>=` stops at a `Left`): `>>=`, `>>`, `pure`, `fmap`, mtl's
`get`, `put`, `modify`, `modify'`, `gets` and `throwError`, and
`runExceptT` is the term itself; `ExceptT e Identity` is `Either e`. At
`ReaderT r Identity` (`Reader r`): ReaderT's newtype, `r -> m a`, so a
function of the environment, `R -> A`, with the prelude's `hs.rd.*`:
`>>=`, `>>`, `pure`, `fmap`, `<*>` (as `>>=`), mtl's `ask`, `local`
(transformers' too), `asks` and `reader`; at `ReaderT r (Either e)`, `R ->
Either E A`, the prelude's `hs.rde.*` (`>>=` stops at a `Left`), those and
`throwError`. `lift` at `ReaderT r` is the inner monad's term under an
environment it ignores, and `runReaderT` and `runReader` are the term
itself. At `WriterT w Identity` (`Writer w`, lazy or strict): WriterT's
newtype, `m (a, w)`, so a result and its log, `A & W` (an `&2` pair),
with the prelude's `hs.wr.*`; at `WriterT w (Either e)`, `Either E (A &
W)`, the prelude's `hs.wre.*` (`>>=` stops at a `Left`): `>>=`, `>>`,
`pure`, `fmap`, `<*>` (as `>>=`), `liftA2` and `throwError`. Each of
those defs takes w's `mempty` and `<>` (a function of two logs) after W
(and E), the fold writing them at w's type (see "Containers"): `pure`
logs `mempty`, `>>=` joins the two logs with `<>`. `writer` is `pure` at
the inner monad of the pair, `lift` at `WriterT w` is `fmap` at the
inner monad of a pair with `mempty`, and the constructor `WriterT`,
`runWriterT` and `runWriter` are the term itself (a pattern `WriterT p`
is `p`). At State, at ExceptT over State, at Either and at Maybe,
Control.Monad's `mapM_`/`forM_`/`traverse_`/`for_`, `mapM`/`forM`/`traverse`
(at a list), `foldM`, `filterM` and `zipWithM_` are the prelude's (the
function a template, so a closed one): State's and ExceptT's in the
module's prelude, Either's and Maybe's prelude/HsMonad.bend's, which walk
the whole list and answer its first Left (Nothing), GHC's answer, and at any of these monads `when`,
`unless`, `void`, `=<<` and `*>` are written with their `>>=`, `pure` and
`fmap`. At `ParsecT`, see "Parsers". Other monads (`ExceptT` over
anything else, `IO`, a type variable) and `<*>` at ExceptT are out.

## Parsers (megaparsec)

Telomare's parser is megaparsec 9.7.0 at `Parsec Void String`. A
`ParsecT e s Identity a` is HsPrelude's parser, a function of the state
to a reply, `HsPcSt -> HsPcRep<A>` (`prelude/HsPc.bend`): the state is the
input left, its offset, line, column and source name; the reply is
megaparsec's four continuations as one value (consumed or not; a result
with its hints, or an error). Errors are megaparsec's (TrivialError's
unexpected and expected items as sets, FancyError's `fail` and incorrect
indentation), merged and hinted as `Text.Megaparsec.Internal` does, and
`errorBundlePretty` prints them as megaparsec does (tab width 8; a wide
character counts one column here, two there). `Pos` is a Nat,
`SourcePos` HsPcPos, `ParseErrorBundle` HsPcBundle.

- What runs a parser once is HsPc's: `>>=`, `>>`, `*>`, `<*`, `<$`, `<$>`,
  `pure`, `<*>`, `<|>`, `empty`, `fail`, `try`, `<?>`/`label`, `hidden`,
  `lookAhead`, `notFollowedBy`, `eof`, `satisfy`, `char`, `single`,
  `string`, `anySingle`, `space1`, `getOffset`, `getSourcePos`,
  `between`, `optional`, `option`, the Lexer's `lexeme`, `symbol`,
  `skipLineComment`, `indentLevel`, `incorrectIndent`, `decimal`,
  `charLiteral` (GHC's `readLitChar`), `runParser`, `errorBundlePretty`,
  `unPos` and SourcePos's fields.
- What runs a parser again, or hands one to a function (`many`, `some`,
  `sepBy`, `sepBy1`, `manyTill`, `skipMany`, `skipSome`, the Lexer's
  `space`, `lineFold`, `indentGuard`, `skipBlockCommentNested`), is cata's
  model, `prelude/Cata/Parsec.hs`: those packages' definitions in Haskell
  at `Parsec Void String`, exported with the package (its file first among
  ARGS' modules after `prelude/Cata/Base.hs`, `-iprelude` among the
  flags). The specialiser writes a
  call of one as a call of the model's def (`sp.pc`), so it is the
  package's own code: rule 15 copies it at its known parser arguments,
  and the parsers that call back into it are one group with them.
- `choice` at a literal list (or at `f <$> [..]`) is `<|>` down the list
  to `empty`; `uncurry g p` with g the model's is `g (fst p) (snd p)`.
- A parameter of a parser type is a function parameter (rule 15 copies at
  it); a lambda applied to an argument (a copy of `lineFold` applies its
  action) is its body with the argument (`sp.beta`); a local binding
  generalised over a type (Haskell 2010's `where check x = .. fail ..`)
  used at one type is the binding at that type (`sp.pl`).
- A def whose answer is a parser takes the state as its last parameter,
  `pc_s0`, and answers the reply (the fold's `fd.eta`); each other use of
  it is the lambda `pc_s => X(.., pc_s)`. So a grammar's parsers, which
  call each other, are a group like any other (`.mu`, with fuel), whose
  answers are Data, and no closure is run twice. A local value that names
  itself (`go = do .. go ..`) is lifted as a def of no parameters, which
  the gate fuels.
- Data.Char's `isAlpha`/`isLetter`, `isAlphaNum`, `isUpper`, `isLower`,
  `isSpace` and `isDigit` are HsChar's (`prelude/HsChar.bend`: GHC's
  answers as ranges of code points, written by
  `tools/char-table/CharTable.hs`); `maxBound` and `minBound` at Int are
  2^48 - 1 and -(2^48 - 1): an HsInt is a sign and a Nat, and Bend's
  runtime holds a Nat up to its largest immediate, 2^48 - 1 (one past it
  stops the run), a range Haskell 2010 allows (at least 2^29 - 1).
- `tests/telomare/run.sh SRC PKG FILE.tel..` runs telomare's
  `runParseModule` under GHC and in cata's Bend (PKG: a `--package`
  output through Telomare.Parse) on each file, and compares the skeletons
  (`Skel.hs`, `skel.bend.part`: each item's kind, names, the spans of the
  names and of the body's root, or the error's text).

`prelude/*.bend` are written into HsPrelude.bend by the fold, from
`bend/Prelude.bend`, which `tools/prelude-text.sh` writes from them.
Tests: `tests/hs/Pc.hs` (a grammar of telomare's shapes: a lexer, `try`,
`choice`, `sepBy` through brackets, a `lineFold`, `manyTill` at a local
indentation, mutually recursive parsers, error messages);
`tests/pc/run.sh` checks the model against megaparsec on 4,004 inputs and
HsPc against megaparsec on 28 parsers.

## Containers

`Data.Map`'s `Map k v` and `Data.Set`'s `Set k` (`IntMap v` is `Map Int v`,
`IntSet` `Set Int`) are HsPrelude's `HsMap<K, V>` and `HsSet<K>`: the pairs
(the keys) in ascending order of the key, each key once, so two equal maps
are one term and `==` at them is HsPrelude's `HsMap.eq`/`HsSet.eq`. The
functions are Data.Map's semantics on that list, not its balanced tree's
cost: `empty`, `singleton`, `insert`, `insertWith`, `lookup`, `member`,
`notMember`, `findWithDefault`, `delete`, `adjust`, `toList`/`toAscList`/
`assocs`, `fromList` (and the Asc ones), `fromListWith`, `elems`, `keys`,
`keysSet`, `size`, `null`, `union`, `unionWith`, `difference`, `map`,
`mapWithKey`, `filter`, `filterWithKey`, `foldr`, `foldrWithKey`,
`intersectionWith`, `restrictKeys`, `withoutKeys`, `fromSet`,
`unionWithKey`, `unionsWith` (of a list) and `split`
(`prelude/HsMapMore.bend`); at Set the same names that exist there,
`unions`, `\\`, `map` and `intersection`; `<>` at a Map or a Set is
`union`. Each takes compare at the key as a template: `Nat.cmp`
at Int, HsPrelude's `HsCmp.char`, `HsCmp.bool`, `HsCmp.unit`, and
`HsCmp.list`, `HsCmp.pair`, `HsCmp.maybe` given compare at the parts (a
String key is a list of Char). A key of any other type (the module's own,
whose `compare` is not written yet) is out, `fold:ord-at-type`.

In the specialiser's output (a package through `spec`) `Int` and `Integer` are
HsPrelude's `HsInt`, an integer: `Pos{n}` is n, `Neg{n}` is -n (n at least
1), one term per integer; `-`, `negate`, `abs`, `signum`, `subtract`,
Haskell's `div`, `mod`, `quot` and `rem`, `^`, comparisons, `show`, `succ`,
`pred`, `toEnum`, `fromEnum`, `fromIntegral` and `toInteger` between them,
literals and literal patterns below zero; `IntMap v` is `Map HsInt v` and
`IntSet` `Set HsInt`. Int's 64-bit wrap-around is not written: F's Int
is exact, right wherever a run stays in Int's range (`adj/`, section 8,
proves that, and that it is wrong where a run overflows). A single
module (hs1003) keeps Int as Nat, where nothing subtracts.

A module alone (tests/hs, hs1003) skips spec, but survey, fold and law
read every export through spec's local-pattern-binding rewrite (sp.pb,
Survey's sv.read), so its `let (a, b) = e` and `let !x = e` fold as a
package's do.

crypton's `Digest SHA256` is HsPrelude's `HsDigest` (its 32 bytes): `hash` is
SHA-256 written in Bend, `show` its hex text, `==` and `compare` its bytes'
order (crypton's); a ByteString is a list of `Word8` (Bend's U32), `pack`,
`unpack`, `toStrict` and `fromStrict` the list itself, Data.ByteArray's
`unpack` at a digest its bytes, utf8-string's `encode` UTF-8.

Data.Void's `Void` is Base's `Empty`, `absurd` `Empty.absurd`, `==` at it `True`.

`Rational` (Data.Ratio's `Ratio Integer`, either name) is HsPrelude's
`HsRational` (`prelude/HsRational.bend`): `HsRational{num: HsInt, den:
Nat}` in lowest terms, den at least 1, as GHC keeps it, so equality is the
fields'. `+`, `-`, `*`, `/`, `negate`, `abs`, `signum`, `compare` and the
other comparisons, `fromInteger`, `fromIntegral` from Int, literals (`2`,
and `0.5` as `1 % 2`), `numerator`, `denominator`, `%`, `show` and
`showsPrec` (GHC.Real's: `(-3) % 2`), and `gcd` and `lcm` at Int and
Integer. Euclid's gcd is fuelled by its second argument. A zero
denominator (GHC's error) answers 0, the type's default.

A list comprehension is the report's translation (3.11): `[e | b, Q]` is
`if b then [e | Q] else []`, `[e | p <- l, Q]` `concatMap (\p -> [e |
Q]; _ -> []) l` (the wildcard when p can fail), `[e | let ds, Q]` `let ds
in [e | Q]` (Spec's `sp.lc`). The lambda's argument type is l's element
type when l is a local of known type, else p's (a variable's, a tuple's, a
constructor's: base's list, Maybe or Either, a package's the type of its
name). `concatMap` at a list is Base's model's (`prelude/Cata/Base.hs`), so
the lambda, which names the earlier generators' variables, is copied.

## Lists, Maybe, Either, pairs

base's list, Maybe, Either and pair functions are HsPrelude's `HsList`, with
Haskell's answers on finite lists: `fst`, `snd`, `swap`, `uncurry`, `zip`,
`zip3`, `zipWith`, `zipWith3`, `unzip`, `lookup`, `takeWhile`, `dropWhile`,
`span`, `break`, `partition`, `find`, `notElem`, `nub`, `nubBy`,
`isPrefixOf`, `isSuffixOf`, `isInfixOf`, `stripPrefix`, `intersperse`,
`intercalate`, `lines`, `unlines`, `words`, `unwords`, `sort`, `sortBy`,
`sortOn` (stable, as Haskell's), `group`, `groupBy`, `tails`, `inits`,
`mapMaybe`, `catMaybes`, `isJust`, `isNothing`, `listToMaybe`,
`maybeToList`, `lefts`, `rights`, `partitionEithers`, `isLeft`, `isRight`,
`fromLeft`, `fromRight`, `foldr` and `foldl` (the function may copy the
element); `==` or `compare` at the element a template, as at a Map's key.
`zip [n ..] xs`, `zip xs [n ..]` and the same with `zipWith` (an endless
list the zip ends) are HsList's `zipFrom`, `zipR`, `zipWithFrom`,
`zipWithR`, the specialiser's rewrite. Data.Bifunctor's `first`, `second`
and `bimap` at Either and pairs (their functions plain, not templates: each
is called once, so a lambda over locals is in); `mempty` at lists, Maps,
Sets, Ordering and (); `flip`; `liftM2` as `liftA2`; `trace` its second argument (the
message to stderr not modelled); `<*>` at Maybe, Either and ExceptT over
State as `>>=` and `fmap`, a chain `f <$> a <*> b <*> c` (or `pure f <*>
..`) as `a >>= \x -> b >>= \y -> fmap (f x y) c`, so that no Maybe or
Either holds a function (a function is `Type`, their parts `Data`);
`sum` and `product` at Int and Integer (HsInt) as at Nat. Foldable's
functions at a Set are at its elements, at a Map at its values (in key
order), as Data.Foldable has them, and `fmap` at a Map its `map`.
Data.Sequence's `Seq a` is a list (front first) and `ViewL a` too
(`EmptyL` the empty list, `x :< s` a cons): `empty`, `|>`, `<|`, `viewl`,
`fromList`.

`iterate f x !! n` is Base's model's `iterateIndex f x n` (the
specialiser's rewrite): f applied n times to x, the endless list never
built, a negative n `(!!)`'s error (a partial function: see "Partial
functions"). `until p f x` is Base's model's `until`,
base's definition, copied at its known p and f and written with fuel (see
"Recursion Bend refuses: fuel"; a fixpoint loop, as Resolve's
`pruneBindings`). Alternative's `<|>` and `empty` at Maybe:
the first `Just`, the second argument a thunk (Haskell's `<|>` is lazy in
it), and `Nothing`. base's instances at pairs, `(,) w`, are Base's model's
defs, the specialiser's rewrite of a method whose class type is `(,) w`:
`fmap` and `<$>` (`pairFmap`), `pure` (`pairPure`, `mempty`), `<*>`
(`pairAp`, `<>`), `liftA2` (`pairLiftA2`) and `traverse` (`pairTraverse`),
at w then the method's types; `g <$> y <*> x` there is `pairLiftA2 g y x`,
so no pair holds a function. A copy of one at w is at w's own Monoid (a
package's instance, as Resolve's `DeferMap`), as any def with a class is.
free's instances at `CofreeF f a` (a Cofree's layer) are Base's model's
defs the same way, at f and a then the method's types: `fmap` and `<$>`
(`cofreeFFmap`), `traverse` and `mapM` (`cofreeFTraverse`), `sequence` and
`sequenceA` (`cofreeFSequence`, free's `traverse id`), `foldr`
(`cofreeFFoldr`), the layer's own `traverse` and `foldr` the package's
instance. Data.Foldable's `fold` at any container is Base's model's
`foldMonoid`, `foldr (<>) mempty` (the same value at a lawful Monoid), at
the container and the Monoid: `foldr` at a list, a Map, CofreeF or a
package's instance (a derived one's own; at a type whose variable is
phantom, as telomare's AbortableF, GHC leaves base's default, `$dmfoldr`,
which is the model's `foldrDefault`, `foldr` over the list `foldMap (\x
-> [x])` gives, and the instance's `$cfoldr = $dmfoldr`, a generated
method with no parameters that is a function, takes them: `$cfoldr f z t
= foldrDefault f z t`, so that f reaches it as a template), `<>` and
`mempty` at lists, Maps and Sets. `foldMap f` at a list is
`foldMapMonoid f`, Foldable's default, `foldr (\x acc -> f x <> acc)
mempty`, at the list, the Monoid and the element (at a package's derived
Foldable it stays the instance's), and GHC.List's `filter` is the
model's `filter`, base's definition: both are copied at a known function
argument.

A view pattern `(f -> p)` is a plain pattern when f is known (the
specialiser's `sp.p3`): `id`, a constructor, `pure` at Maybe, a
projection `\(C .. x ..) -> x`, a selector `\case C .. x .. -> Just x; _
-> Nothing` (its answers through casts, `pure` as `Just`), a composition
of those, Recursive's `project` and Corecursive's `embed` at Fix and
Cofree, and a class's method whose class types are known (its instance's
body, the method's own types free), as telomare's pattern synonyms'
`extractB`, `extractL` (an instance with associated types: casts),
`extractS`.

Show at base's types is HsPrelude's `HsShow`, GHC.Show's text: `showsPrec`,
`show` and `shows` at Int (HsInt; a negative number in parentheses above
precedence 6), Char and String (GHC's escapes: `\n`, `\DEL`, `\SOH`,
`\1234\&5`, `\SO\&H`), Bool, (), lists and Maybe; `showString`, `showChar`,
`showParen`, `showSpace`, `showCommaSpace`, `showList__`. A derived Show
instance of the package's own types (GHC's generated `showsPrec`, its
literals bare Ints the specialiser makes HsInt) is copied at its type like
a hand-written one, and base's default `show` and `showList` given it are
HsPrelude.Z's `showVia` and `showListVia`. So are derived Functor, Foldable
and Traversable instances (GHC's generated `fmap`, `<$`, `foldr`,
`foldMap`, `null` and `traverse`: constructors, lambdas and the fields' own
methods). Show at Fix f (data-fix's instance, through f's Show1) is Base's
model's `fixShowsPrec` (`show`, `shows`, `showList` with it), copied at f: a
fold to the text a node shows unparenthesised, `showParen (d >= 11)` at
precedence d, its children's text handed to `liftShowsPrec` at the
precedence it asks for (exact when the Show1 only prepends text; the laws
hold it to GHC's), f's Functor needed for the fold. Show at a list or a
Maybe of the package's own type or of a Fix, at Map and Set: out.

GHC.Prim's `coerce` (a newtype's derived instance, GeneralizedNewtypeDeriving,
is coerce of its field type's, and the specialiser copies it as it copies
a hand-written one) is the term at one type, a newtype's constructor to
it, its selector from it (a newtype without a field name: out,
`fold:coerce-at-type`), and at function types the argument coerced back
and the answer forth.

## Lifting

Bend matches only parameters and pattern fields, not a local or a computed
value, and no match may follow a local statement; a lambda holds one
expression. So these become defs of their own: a `case` on a computed value
or in an argument, a lambda whose body is a `let` or a `case` (or whose
patterns are not all variables, as a `\case` or `\cases`), a local value
whose body is one, a `case` after a `let`, and every `where` or `let`
function (one that calls itself too). A lifted def is `NAME.lK`
(`NAME.go` for a local `go`); its parameters are the enclosing def's type
variables, the locals its body uses, with the types GHC gave their
binders, and its own. A use of a local function becomes a call of its def
with those locals first. The ledger says `ok-gen` for a lifted def; a
lifted def that calls the def it came from is in a cycle of calls with it
(see "Recursion Bend refuses").

An `if` or a `let` that is an application's argument or function part
goes out over it first (the specialiser's `sp.ifl`): `f (if c then a else
b)` is `if c then f a else f b` and `f (let ds in e)` is `let ds in f e`
(the locals are numbered apart; the values are the same), so that the if
is where its type is known, a body's or a branch's (EAL's `mergeClasses`:
`pure $ if la >= lb then a else b`). Not over `&&` and `||`, lazy in
their second argument, and not out of a lambda or a `case` (an if there
is still `fold:if-in-argument`). Out of a tuple's element too
(`sp.ifl.tup`): `(.., let ds in e, ..)` is `let ds in (.., e, ..)` and
`(.., if c then a else b, ..)` is `if c then (.., a, ..) else (.., b,
..)` (Bend builds a tuple's elements with the tuple), as a record update
in a pair is (Fast's `tickApply`: `(m { fmApplies = .. }, f)`).

A local named as one of its module's own defs that its top-level binding
refers to is renamed `NAME_ID` (its GHC unique; `sp.lr`): GHC's record
update binds the new field's value to a local named as the field, and
the update's right side then calls the field's selector (EAL's
`freshInt`: `st { esNextVar = esNextVar st + 1 }`), which Bend would read
as the local.

A record pattern `C {}` at a constructor without field names is `C{_,
..}`, a wildcard for each field (IC's `valueKind`: `ICRef {}`). The
prelude's `hs.maybe` and `hs.either` take their answer's type as a
`Type`, so a monad's action (a function) is one (EAL's `walkTau`:
`maybe (pure t) walkTau`).

## Partial functions

Haskell's partial functions are failure values, as telomare's bend
branch writes its crashes: `error`, `errorWithoutStackTrace`,
`undefined`, `head`, `tail`, `last`, `init`, `!!`, `fromJust`,
Data.Map's `!`, and Foldable's `maximum`, `minimum`, `maximumBy`,
`minimumBy`, `foldr1` and `foldl1` at a list are prelude/HsPartial.bend's
`HsList.error`, ..., `HsMap.at`, `HsList.maximum`, ..., each answering `Either<&2, &2, String, A>`: `Inl{GHC's
message}` where GHC throws its `ErrorCall` (the message alone, as
`ErrorCall m` matches it: "Prelude.head: empty list", "Map.!: given key
is not an element in the map"), `Inr{the answer}` else. The survey takes
them (info `partial:NAME`, not out). `xs !! n` is `HsList.index` at an
HsInt index in a package (Spec writes it `HsPrelude.Z.!!`), and
`HsList.index.go` at a Nat one in a module alone, where Int is Nat.

So are `div`, `mod`, `quot` and `rem` by a divisor that is not a known
non-zero literal, and Rational's `/`: GHC throws an `ArithException` at
0 ("divide by zero", "Ratio has zero denominator"), and Base's `Nat.div`
and `Nat.mod` answer 0 and x there, so F wrote programs more defined than
Haskell's and, adj/ proves, was no left adjoint. Fold's `fd.num` calls
HsPartial.bend's `HsNum.div`, `HsNum.mod` (at Nat), `HsNum.idiv`, `imod`,
`iquot`, `irem` (at HsInt) and `HsNum.rdiv` instead, failure values at 0;
by a non-zero literal (``n `div` 2``, and `flip div 2`, decided at the
flip), or by a variable an enclosing if has told is not 0 (``if x == 0
then .. else .. a `div` x ..``, and `x /= 0`, `x > 0`, `0 < x`: Fold's
`fd.nzg`, before the partial pass), the total ones stay.

A def that calls one, or calls a def that does (the module's items to a
fixed point, then the later modules' through the package's exports), is
partial (Fold.bend's pass `fd.pt`, after the local catas, before the
groups): its answer type is the Either, and its doc says so. In each
answer, a body's, a case's or an if's thunk's, its partial calls are
bound innermost first with `hs.either.bind(String, A, R, call, x =>
...)`, A the callee's answer read off its signature with the call's type
arguments put in, and the answer is `Inr{..}`; an answer that is itself
a partial call is that call, and an if (a compare's three ways) with a
partial branch is an if of Eithers (bound as one call where it is not
the answer). A let's partial calls are bound before it, the let then a
parenthesized body inside the last bind's lambda. Bend is strict, so a
partial call's error would be the def's even where Haskell's laziness
never forces it; before the partial pass Fold's float-in (`fd.fi`)
moves a let into the one branch of an if that uses it (on down, as deep
as it goes; `let x = v in x` is v), drops a let nothing uses, and takes
`fst` and `snd` of a pair written out, as GHC's own float-in moves them:
`let h = head xs in if n == 0 then 0 else h` errs only where it takes h
(tests/hs/Lazy.hs). A let both branches use stays. A strict one, `let
!x = e`, must not move: hs-export writes it as the pattern binding it
means, `(patbind (pbang (pvar x)) ..)`, which Fold does not take yet
(`fold:form`, tests/hs/Bang.hs). What a lazy list needs, map's elements
left unforced, is out; the laws compare.
Where two partial calls of one def both fail on an input, GHC may throw
either (its exceptions are imprecise) and cata gives the first it binds:
the laws compare messages, so such a def can be out on a law
(tests/hs/PartialFold.hs's `range`).

A partial call under a lambda (a monad's continuation, a function
argument, a cata's algebra) is out for now (`fold:partial-in-lambda`).

A partial def's law runs GHC's call under `LawEw`, whose `lawSx` turns
an `ErrorCall m` into `Inl m` (an `ArithException` into `Inl` of its
show) and an answer into `Inr`, so the laws check GHC's message too
(tests/hs/Partial.hs, tests/hs/DivZero.hs).

## Equality

Haskell's `==` and `/=` at a type Base has no `==` for: at lists, Maybe,
Either, pairs, `()` and Ordering the prelude's `hs.eq.*` (templates given
`==` at the parts, written into a module that uses one); at a type of the
module whose Eq instance GHC derived, `T.eq` (`ok-gen`): the same
constructor and `==` at each field, as GHC derives it, and a template
`T.eq(~A.., ~eq_A.., a, b)` when T has parameters. `elem` at such a type is
`List.contains` given that `==`. Out, each with its reason: a type whose Eq
instance is written by hand (`fold:eq-instance`); a type inside a list or a
Maybe of its own (`fold:eq-nested`: the call of T.eq sits in a template
argument, where Bend sees no decreasing call) or two types calling each
other's (`fold:eq-mutual`); a type of an earlier module whose T.eq is out
(`fold:eq-imported:NAME`); `==` at a type variable (`fold:eq-at-tyvar`) and
`<`, `compare`, `max`... at any of these types (`fold:ord-at-type`).

## cata as a functor: the cache, the way back, the squares

PLAN.md's "cata as a functor" says what holds and what does not, with
numbers. In short: hs2bend is F, from Haskell's programs to Bend's;

- **The cache** (`bend/Cache.bend`, `CATA_CACHE=DIR`): F is compositional
  over a package's modules, so law keeps each of bend's checks under the
  SHA-256 digest of the file and of its imports (a Merkle DAG over the
  package) and each of GHC's answers under the digest of its script and
  the sources it reads; a run checks again only what changed. With
  `CATA_CACHE` unset law is as it was (`tests/cache/run.zsh`,
  `tests/cache/cross.zsh`: the same files byte for byte, with and without a
  cache, and with a cache another version of the rules filled).
- **The way back** (`bend/Back.bend`, G, bend2hs; `CATA_BEND2HS=1`): law
  also writes each module's kept items as Haskell, `OUT/hs/NAME.hs`, with
  prelude/Back/BendRt.hs giving Base's and the prelude's names their
  Haskell meaning. `tests/back/run.zsh LAW WORK FILE...` runs each module's
  laws' GHCi script against G(F(h)) and compares, law by law, with h's
  answers: the same, more defined (h errs, G(F(h)) answers: F makes a
  partial h total: ``x `mod` 0`` errs, Bend's `Nat.mod(x, 0n)` is x),
  different, or missing.
  G(F(t)) is t only up to an iso (h's triple is G's nested pair, a partial
  h's answer an Either), which BendRt's `b'up` undoes at h's type.
  The other half, F(G(b)) against b (`tests/back/round.zsh`,
  `bend/Round.bend`): G's Haskell through hs-export and law again, each
  def compared with b's by its text (names as F writes G's, parameters
  by position) and, where the text differs, by b's laws; Fold's `fd.rt`
  takes BendRt's wrappers back to the defs they stand for, a law each.
- G gives h's types back where F loses them: a data field's Int, Integer
  or Natural (all Nat in Bend) through h's synonyms, a type's kind
  variables dropped, and a constructor with a tuple of 3 or more (Bend's
  nested pairs) reached through a pattern synonym that converts it; a
  module's own type with parameters has its iso as a map over its fields
  (b'map'D), and the numbers in the fold's own recursion types (.mu.In,
  .mu.Out) are type parameters GHC infers.
- On a package (`tests/telomare`: back.zsh, laws.zsh): G writes each
  module as the package's, other modules' names qualified and imported,
  and BendRt.hs (with BendPc.hs, cata's megaparsec model) has the
  prelude's Map, Set, SHA-256, Show, Rational and monads. Telomare: all
  31 of G's modules compile, and its 420 laws are 420 the same, 0 differ.
- **Naturality** (`tests/natural`): the specialiser's copies of a def at
  several types, counted once their types are erased (`Copies.hs`), and a
  copied def written once, with a law proved once and a copy as its
  instance (`bend --verdict`). Spec writes a copy of a global def at its
  types once per package: a module that imports the module that wrote it
  names that one (telomare: 258 copies fewer, the same results).
- **Squares** (`tests/square`): a hand-written Bend function against F of
  the Haskell one, `phi(F.h(x)) == W.b(phi(x))` proved for every x
  (xmonad-bend's StackSet against cata's XMonad.StackSet, all 17 squares by
  `--verdict` since the fold copies map at a known function, fd.hm; its
  Core's default config against XMonad.Config).
- **The checker** (`tests/adjoint/run.zsh SQDIR LAWOUT MOD WORK
  DIR=PATH...`, `bend/Adj.bend`): any such pairing, on both sides: the
  squares' proofs (`--check-only`, `--verdict`), and each square at GHC's
  own answers for h (law's example laws, h(a) == v, give phi(v) ==
  W.b(phi(a)), checked by bend), with mutants (two squares of one shape,
  their b's swapped) at GHC's answers and in the proofs.

## Build

    nix build .#hs-export .#survey .#fold .#law .#ghc
    ln -s ../../agda2bend/bend bend/a2b      # a checkout's link, for bend itself
    nix run .#bend -- bend/Survey.bend --check-only
