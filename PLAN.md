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
