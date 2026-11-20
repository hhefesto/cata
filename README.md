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
- Defs that call each other are one def, `HEAD.mu(fuel_, in_)`, as the
  bend branch's mutual walks are: `HEAD.mu.In` has a constructor for each
  member holding its arguments, and the answer is theirs when they share
  it, else `HEAD.mu.Out`'s constructor for the member (`HEAD.mu.outK`
  takes it out). Each member is a call of `HEAD.mu` at its constructor. A
  group whose members take type or template parameters, or do not fold
  whole, is left as it was.

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
the fold reads a method at its type.

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
State and at ExceptT over State, Control.Monad's `mapM_`/`forM_`,
`mapM`/`forM`/`traverse` (at a list) and `foldM` are the prelude's (the
function a template, so a closed one), and at any of these monads `when`,
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
  ARGS' modules, `-iprelude` among the flags). The specialiser writes a
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
  2^63 - 1 and -2^63.

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
`mapWithKey`, `filter`, `filterWithKey`, `foldr`, `foldrWithKey`; at Set
the same names that exist there, `unions`, `\\` and `map`; `<>` at a Map
or a Set is `union`. Each takes compare at the key as a template: `Nat.cmp`
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
`IntSet` `Set HsInt`. Int's 64-bit wrap-around is not modelled. A single
module (hs1003) keeps Int as Nat, where nothing subtracts.

crypton's `Digest SHA256` is HsPrelude's `HsDigest` (its 32 bytes): `hash` is
SHA-256 written in Bend, `show` its hex text, `==` and `compare` its bytes'
order (crypton's); a ByteString is a list of `Word8` (Bend's U32), `pack`,
`unpack`, `toStrict` and `fromStrict` the list itself, Data.ByteArray's
`unpack` at a digest its bytes, utf8-string's `encode` UTF-8.

Data.Void's `Void` is Base's `Empty`, `absurd` `Empty.absurd`, `==` at it `True`.

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
and `bimap` at Either and pairs; `mempty` at lists, Maps, Sets, Ordering
and (); `flip`; `liftM2` as `liftA2`; `trace` its second argument (the
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

Show at base's types is HsPrelude's `HsShow`, GHC.Show's text: `showsPrec`,
`show` and `shows` at Int (HsInt; a negative number in parentheses above
precedence 6), Char and String (GHC's escapes: `\n`, `\DEL`, `\SOH`,
`\1234\&5`, `\SO\&H`), Bool, (), lists and Maybe; `showString`, `showChar`,
`showParen`, `showSpace`, `showCommaSpace`, `showList__`. A derived Show
instance of the package's own types (GHC's generated `showsPrec`, its
literals bare Ints the specialiser makes HsInt) is copied at its type like
a hand-written one, and base's default `show` and `showList` given it are
HsPrelude.Z's `showVia` and `showListVia`. Show at a list or a Maybe of the
package's own type, at Fix (through Show1), at Map and Set: out.

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

## Build

    nix build .#hs-export .#survey .#fold .#law .#ghc
    ln -s ../../agda2bend/bend bend/a2b      # a checkout's link, for bend itself
    nix run .#bend -- bend/Survey.bend --check-only
