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

## Build

    nix build .#hs-export .#survey .#fold .#law .#ghc
    ln -s ../../agda2bend/bend bend/a2b      # a checkout's link, for bend itself
    nix run .#bend -- bend/Survey.bend --check-only
