# cata

Checked Bend 2 by fixed rules: Haskell, Agda and specs in, Bend out. No
model takes part; a module the rules cannot translate is ledgered with its
reason. PLAN.md has the decisions, the steps and what has been measured.

## Parts

- `tools/hs-export` (Haskell, GHC 9.10.3's API): `hs-export OUT.sexp
  FILE.hs` type-checks one module and writes its typechecked syntax, every
  binder's type and every instance GHC chose, as S-expressions
  (`tools/hs-export/FORMAT.md`). It decides nothing.
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

## Monads

GHC hands a do block over as its `>>=` and `>>`, and cata writes those at
the monad they are at. At `Maybe` and `Either e`: Base's `Maybe.bind` or
the prelude's `hs.either.bind`, with the rest of the block as a closure;
`return`/`pure`, `fmap`/`<$>`, `maybe`, `either` and `fromMaybe` too. At
`State s` (`StateT s Identity`, lazy or strict): a function of the state to
a result and the next state, `S -> A & S` (an `&1` pair, so the result may
be a function, as at `<*>`), with the prelude's `hs.state.*`: `>>=`, `>>`,
`pure`, `fmap`, `<*>`, mtl's `get`, `put`, `modify`, `modify'` and `gets`,
and `evalState`, `execState` and `runState`. Other monads (`ExceptT`,
`ParsecT`, `IO`, a type variable) are out.

## Lifting

Bend matches only parameters and pattern fields, not a local or a computed
value, and no match may follow a local statement; a lambda holds one
expression. So these become defs of their own: a `case` on a computed value
or in an argument, a lambda whose body is a `let` or a `case` (or whose
patterns are not all variables), a local value whose body is one, a `case`
after a `let`, and every `where` or `let` function (one that calls itself
too). A lifted def is `NAME.lK` (`NAME.go` for a local `go`); its
parameters are the enclosing def's type variables, the locals its body
uses, with the types GHC gave their binders, and its own. A use of a local
function becomes a call of its def with those locals first. The ledger
says `ok-gen` for a lifted def; a lifted def that calls the def it came
from makes the two mutually recursive, which Bend refuses (both out).

## Build

    nix build .#hs-export .#survey .#fold .#law .#ghc
    ln -s ../../agda2bend/bend bend/a2b      # a checkout's link, for bend itself
    nix run .#bend -- bend/Survey.bend --check-only
