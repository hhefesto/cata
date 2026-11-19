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
- Shared with agda2bend: its Bend syntax tree, printer and S-expression
  reader (`ToBend/`) and `Sys.bend`, as `bend/a2b`.

## Build

    nix build .#hs-export .#survey
    ln -s ../../agda2bend/bend bend/a2b      # a checkout's link, for bend itself
    nix run .#bend -- bend/Survey.bend --check-only
