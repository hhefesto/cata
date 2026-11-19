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
