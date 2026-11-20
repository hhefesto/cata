# cata: plan

cata writes Bend 2 by fixed rules. ana unfolds Bend from what she learned;
cata folds a structure into Bend, so every file it writes can be rebuilt
exactly from its input, and every file is checked by `bend`.

## Decisions (the user, 2026-11-19)

- **What cata is:** one deterministic Bend writer, with Haskell (new), Agda
  (agda2bend's fold) and specs as its inputs.
- **The 361 modules Codex translated (hs2bend):** kept as training data,
  labelled as Codex's, but never used inside cata: not as a reference, a
  template or a test oracle.
- **Step 1:** on olimpo's CPU, reading only, with no AI and nothing rented.
  "Work on all your recommended steps."

## Rules that hold everywhere

1. No AI inside cata's loop. A module the rules do not take goes to the
   ledger with its reason, and the rules are fixed; no model repairs it.
2. Laws are frozen before code is generated, and the generator never edits
   them (Bend's own LAWS.bend / PROOF.bend rule).
3. Three levels of "checks" are never one label: `--check-only`, example
   laws, and a real proof (`--verdict`). The corpus marks which one each file
   has.
4. agda2bend's machine-named output (`x_9`, quantity parameters) is not
   pooled with cata hs's; the back end is shared.
5. Search-made programs are capped and deduplicated.
6. The 176-task test's functions (agent-mugen-eval's held-out units) are
   kept out of specs and translations.
7. No workarounds: no fuel to force termination, no arithmetic split over
   several U32s. Skipping is better.

## Layout

- `tools/hs-export` (Haskell, GHC 9.10.3's API): one module's typechecked
  syntax as S-expressions, `FORMAT.md` its contract. It decides nothing.
- `bend/` (Bend 2.0.39): everything that decides. `bend/a2b` is agda2bend's
  `bend/` (a git-ignored link here, the `agda2bend` flake input in a build).
- `run/` (git-ignored): exports, surveys, gcroots.

## Steps

1. **Measure, on CPU, with no AI.** Done 2026-11-19; numbers below.
2. **cata hs:** the exporter (done), the fold into ToBend's syntax tree, the
   GHC example laws, the ledger. First the 643 modules, then
   run/raw-new/haskell.jsonl's 139,346 files.
3. `prop_` properties as laws; classic-structure specs (the user approves
   their laws).
4. cata spec's search.
5. ana as a proposer inside cata. Renting a GPU needs the user's OK.

## Step 1 results (2026-11-19)

### 1a. Which modules fall in cata hs v1 (hs-export + bend/Survey.bend)

The hs2bend inbox on disk holds 643 modules, not the 1,003 AGENTS.md says
(00001-00664, gaps). GHC 9.10.3 (GHC2021) type-checks 637; 6 fail
(package-qualified imports, packages outside base, extensions their cabal
files turned on).

`survey` judges every binding a user wrote (4,966; derived instances and
record selectors are GHC's and left out) against the v1 subset written at
the top of bend/Survey.bend:

| hs2bend's bucket | modules | all bindings in v1 | all but IO | some | bindings in v1 |
|---|---|---|---|---|---|
| done (Codex passed) | 361 | 108 | 114 | 279 | 1,381 / 2,221 |
| skipped (Codex gave up) | 109 | 1 | 3 | 63 | 376 / 1,276 |
| inbox (not tried) | 161 (+4 GHC errors) | 48 | 49 | 105 | 670 / 1,293 |
| work (half done) | 10 (+2 GHC errors) | 1 | 1 | 6 | 48 / 72 |

So rules alone would take about a third of Codex's 361 whole (114), and
about half of all bindings (2,475 of the 4,862 other than `main`).
This is the survey's judgement of the subset, not a translation: the fold
will lose more.

What keeps the others out (a not-ok binding counts once per group; `calls`
means it calls a binding that is out):

| reason | bindings |
|---|---|
| calls one that is out | 892 |
| polymorphic in a class other than Eq/Ord (`Num a =>`, `Integral a =>`) | 774 |
| a type of the module that is out, or another base type | 500 |
| partial functions (head, tail, !!, fromJust, error, maximum, ...) | 448 |
| recursion that does not visibly shrink | 233 |
| subtraction or negation on Int | 221 |
| Double | 211 (+137 methods at Double/Word) |
| IO and other monads | 172 |
| user classes | 113 |
| laziness (enumFrom, iterate, repeat, cycle) | 103 |
| Word / IntN | 81 |
| recursion through a value (`map f` inside f) | 58 |
| mutual recursion | 37 |

The bindings whose one own reason is that reason (lifting it alone frees
them before calls): partial 260, a type out 165, Int subtraction 117,
non-shrinking recursion 95, `Num a =>` 49, laziness 45, IO 37, `Floating a
=>` 34, recursion through a value 31, `Integral a =>` 25, Double 22.
Monomorphising class-polymorphic functions at the types the module uses
them at is the largest rule after v1.

### 1b. How often ana's bodies pass example laws

Already measured, by `agent-mugen-score` (ana, 2026-11-11): each solved
task's definition is held to the original's on test inputs, `{f(x) ==
f.orig_(x) : R}` by `{==}`. r9-step135000 (run/v9/ev/r9-step135000.f2.avoid,
2026-11-19 07:15):

| shape | passes the check | same as the original | right on the tests | wrong | untested |
|---|---|---|---|---|---|
| direct (67) | 20 | 6 | 2 | 7 (+1 slow) | 4 |
| fill (67) | 34 | 9 + 1 proof | 5 | 10 | 9 |
| repair (42) | 26 | 22 | 1 | 0 | 3 |

Of her direct and fill bodies that pass the check and differ from the
original, 7 were right on the tests and 18 wrong or slow (13 untested). The
check alone overstates her about twofold; a law filter is needed before
anything she writes is kept.

## Step 2: the fold (design, 2026-11-19; built as bend/Fold.bend, see "Step 2 results")

`cata hs FILE.sexp OUT`: the export's v1 bindings into ToBend's syntax tree
(`bend/a2b/ToBend/Ast.bend`), ordered (`ToBend/Order.bend`), quantities
marked (`ToBend/Copy.bend`'s `tcp.decide`/`tcp.finish` with an empty
`QF.TqEnv`, or a smaller pass of cata's own if that one is too tied to
Agda), printed (`ToBend/Print.bend`), then checked; every binding out goes
to `OUT/ledger.tsv` with the survey's reason or the checker's.

What Bend 2.0.39 forces, and the rule for each:

- **No `if`, and `match` only on a parameter or a pattern variable.** A
  guard or an `if` becomes a call of cata's prelude `Hs.if(R, c, u => a, u
  => b)`, branches as thunks, the way Base writes `List.any.if`; a helper
  def would call the function back (mutual recursion, refused). `case` on
  a parameter or a part of one is a `match`; on a computed value, a
  type's eliminator (`T.case`, generated per data type) with the branches
  as lambdas. A recursive call through an eliminator's lambda does not
  shrink to the checker, so such a binding is ledgered.
- **A `let` may not precede a `match` on a parameter.** `where` bindings go
  at the top of each case's body.
- **No mutual recursion; a def calls only defs above it.** Order.bend sorts;
  the survey already ledgers mutual groups.
- **Termination reads arguments left to right.** The parameter that shrinks
  (the survey finds it) is moved first; callers follow the new order.
- **Affine variables.** Data used twice is `+`; a function argument used
  twice must be a template (`~f`), so a call that passes a closure over
  locals is ledgered unless the callee is specialized for it.
- **Haskell's `String` is `[Char]`.** v1 maps every list, strings included,
  to `List<&2, T>`; mapping `[Char]` to Bend's `String` (SNil/SCon) with
  `String` versions of the prelude is a later rule.
- **Int as Nat** only where nothing subtracts or negates (the survey
  marks it); `n + 1` patterns of countdowns are not v1.

Example laws (step 2's oracle): cata (Bend) lists inputs by type, smallest
first and deterministically, writes them both as Haskell and as Bend
literals, writes a Haskell harness that prints each output, runs it with
GHC, and writes `law f.exK: {f(a) == v : R}` with `def f.exK(): {==}`. The
Codex translations are never consulted.

## Step 2 results (2026-11-19, hs1003's 643 modules, olimpo's CPU, no AI)

`run/fold OUT FILE.sexp...` (bend/Fold.bend, compiled with Bend 2.0.39)
writes OUT/NNNNN.bend and OUT/ledger.tsv. Every file it writes passes
`bend --check-only`; that is all "ok" means here (no example laws yet).

| run | functions ok | types ok | out | files |
|---|---|---|---|---|
| fold1 (0b83518) | 1,027 | 489 | 3,828 | 284 |
| fold5 | 1,261 | 558 | 3,525 | 329 |

What changed from fold1 to fold5: the prelude (Bool.if) is written (it
never was); a data type with a field type the fold cannot write is out,
like a def; the module's type synonyms are expanded (all variables at
once), FilePath is String; templates (a function parameter used twice,
and every parameter a template argument names, is ~, moved to the front,
and calls pass ~ there; a closure as a template is out); a local `abs`
(a generalised where-binding with no dictionary) is its one bind, its
value annotated; a local binding the fold cannot write is out (it was
dropped, and its name then resolved to a top-level def of the same name:
fold1-fold4 wrote mult1 = x * y with the module's x and y, not the
where-bound ones. Bend's check cannot see that; example laws will).

Biggest reasons left (fold5): `==` on other types (79), building a
record (52), case on a computed value (50), flip (27), sections (26),
type applications of a variable (24), recursive local groups (23),
local functions (22), do (19), Double (17).

### Example laws (bend/Law.bend, `run/law`, 2026-11-19)

`law OUT FILE.sexp...` folds and gates each module as `fold` does, then
lists inputs for every def the gate kept, by its Haskell type (Int,
Integer, Natural 0..3; Bool; Char 'a' 'b' ' '; lists up to 3 long;
Maybe, Either, tuples, Ordering, unit; the module's own types two
constructors deep; a type variable is Int), at most 8 per def, smallest
first. GHC 9.10.3's interpreter (the flake's `.#ghc`) loads the original
module and runs each call with a 2 s limit, printing the answer as an
S-expression; every name in the script is qualified (`LawP` is the
Prelude), so a module's own Maybe changes nothing. Each answer becomes
`def f.exK() -> {f(Nat, a, b) == v : R}: {==}` in the module's file, and
the gate runs again: a law Bend refuses takes its def out (`law:` and
Bend's first error line), with what uses it. Bend's checker computes both
sides; nothing else is trusted.

hs1003, all 643 modules (run/law3, 6 processes, about 6 minutes):

| | defs |
|---|---|
| check, and every example law holds (`ok-law`) | 1,075 (4,218 laws) |
| of these, no arguments: the one law is the whole def | 415 |
| check, no law (`ok-check`): a function argument | 128 |
| ... a Float argument or result | 41 |
| ... no input (an empty type, a function inside) | 8 |
| ... GHC gave no answer in 2 s (Peano numbers to 10^7) | 7 |
| ... Bend's checker overflowed on an answer (1000000n, a long string) | 2 |
| a law failed | 0 |

No def of fold5 fails its laws. The oracle does catch what the check
cannot: the fold as it was at db802bf (before ac26f36's where fix), run
through the same laws on 00303, loses mult1, mult2, mult3 and waxOn, each
to its first law (`expected : 70n | observed : 30n`: Bend's value of the
translation, then GHC's answer), and keeps the four defs that were right.

What the laws do not cover yet: functions taking functions (128; a
fixed set of small closed functions as inputs is the next rule), Float
(no inputs; F32 answers are not compared), and more than one shape of
input for the module's recursive types (two constructors deep).

### Records, and one gate (2026-11-19, later)

Records are built and taken apart (`reccon`, record patterns, each field's
selector a def of the type's module), and a law whose answer has a run of
5 or more digits is left out (Bend's checker overflows past about 10000n).
Then the gate runs once per module: GHC's answers come first, for every
def the fold wrote, and the defs and their laws are checked together; a
def Bend refuses goes with its laws and with what uses it, a law Bend
refuses takes its def out (`law:`). Only when that one gate keeps no def
while there were laws (Bend died, so no item was to blame) are the defs
gated again alone, with `nolaw:law-gate-failed`.

The gate's closure had a bug: what a dropped item "defines" was its
binders (`T.tba.item.names`: a def's parameters, a type's fields), not
its name and constructors. So dropping `runReader(x)` dropped every item
naming an `x` (00297's `x.ex1`), and kept the items calling `runReader`,
which Bend then refused one round at a time. Now `fd.item.defs`.

hs1003, all 643 modules (run/law7, 6 processes, 53 s; run/law4, the two
gates, took 72 s):

| | defs |
|---|---|
| check, and every example law holds (`ok-law`) | 1,360 (4,781 laws) |
| check, no law (`ok-check`): a function argument | 128 |
| ... a Float argument or result | 44 |
| ... GHC gave no answer in 2 s | 16 |
| ... no input | 13 |
| ... the one gate lost every def | 1 |
| types | 558 |
| out | 3,224 |

The same verdicts as the two gates (run/law4), row for row; 135 reasons
now say `dep:NAME` where they said Bend's `check:` error on the name the
closure had missed. `bend --check-only` runs 510 times (950 before; 0.13 s
of each is Base), GHC 340.

## Packages: telomare master (2026-11-19)

The user: "try passing telomare (master) through cata. Since we already
have a bend version of telomare's master, you can compare and improve
cata. Also improve cata's speed."

`hs-export --package` loads the library's 28 modules (telomare master
0058cf46, `src/`, Haskell2010, the flake's `.#ghc-telomare` package db)
in 4 s and writes each module and `modules.txt` in dependency order.
`survey`, `fold` and `law --package` then read the modules in that order:
a name, constructor, selector, type or synonym of an earlier module of
the package is in when that module kept it (`import:M.NAME` when not),
and is written with that module's file as alias, `Telomare_IR_Loc.x`,
the file imported (`import ./Telomare_IR_Loc.bend as Telomare_IR_Loc`)
when the text names it. A module's file is written in a package when it
keeps any item, types alone too. Its synonyms are folded again in each
module that uses them; its defs' template flags are fixed for callers.

| telomare library (607 bindings) | functions | types | out |
|---|---|---|---|
| each module alone | 65 (54 with laws) | 41 | 798 |
| as a package (run/telomare/law-pk2, 41 s) | 82 (55 with laws) | 67 | 755 |

What it keeps is the leaves: record selectors, constants, small
functions on Loc and Error's records (Loc: `SourcePosition`, `SourceSpan`,
`LocTag`, `LocatedName` and their selectors check, laws from GHC). The
survey puts 562 of the 607 out, and 525 of those for more than one kind
of reason, so no single rule frees many:

| kind of reason (a binding counts once per kind) | bindings |
|---|---|
| calls or imports one that is out | 451 |
| a type outside v1 (EALError's Digest, IR.Base's Fix-built ones, ...) | 363 |
| a monad: ExceptT 232, ParsecT 110, Either 64, StateT 46, Maybe 27, do 146 | 353 |
| a Base function v1 lacks | 207 |
| recursion schemes: Fix, Cofree, Base, `~`, Recursive/Corecursive | 200 |
| Data.Map, Set, IntMap | 137 |
| pattern synonyms (BasicEE, PairB, ... over Fix) | 131 |
| user classes (BasicBase, StuckBase, PrettyPrintable, ...) | 108 |

The names most out-of-package users wait on: EALError (70: a Digest
field), StuckBase and BasicBase (55 each: classes over the base functors),
CompiledExpr (50), ExpandedSurfaceTerm (48), PrettyPrintable (42),
BasicExpr (41: `Fix BasicExprF`).

The bend branch's port (`bend/`, 62k lines, written by hand and by
agents, so never inside cata: rule 1) does what these rules would have to:
Fix and its base functor fused into one recursive type (`type V is Data:
VZero{} VPair{a, b} ...`), state passed and returned explicitly, Int as
U32, String as Bend's String, records with named fields. What cata
writes where both have the def (Loc's records, selectors, constants) is
the same shape with Nat for Int and `List<&2, Char>` for String.

The rules telomare needs, in the order that would free the most: (1) Fix
fused with a base functor of the package into one recursive type, with
`cata`/`embed`/`project` as generated defs, and pattern synonyms that
only build or match constructors inlined; (2) monads: Maybe and Either by
`match` (or Base's `Maybe.bind` on a computed value), State as a state
passed in and returned; (3) class-polymorphic functions monomorphised at
the package's instances; (4) Data.Map with String keys as Base's Map.

Speed, measured with the `bend` and `ghc` calls timed (hs1003): of 331 s
of CPU, `bend --check-only` was 199 s and GHC 132 s; Survey's two
fixpoints (`sv.reach`, `sv.ok.fix`) ran their full fuel (number of
bindings) every time and now stop when a step changes nothing (survey of
telomare 18.3 s to 12.3 s, EAL alone 4.0 s to 1.2 s, the same output).
What is left of cata's own time is mostly reading the exports (about
0.9 s per MB with ToBend/Sexp.bend). In a package, GHC's
`-fobject-code -outputdir DIR` compiles the imports once and `*SRC` keeps
the module interpreted (EAL's laws: 3.1 s, then 1.7 s with the cache).
