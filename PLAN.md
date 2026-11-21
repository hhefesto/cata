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
- `tests/hs`: small Haskell modules a rule was tried on (`hs-export`, then
  `law`).

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

## Telomare's rules, 1: Fix, Cofree and recursion schemes (2026-11-19)

The user: "Which rule should I build next for telomare? All of them in
your recommended order": (1) Fix fused with its base functor, cata/embed/
project generated, simple pattern synonyms inlined; (2) Maybe/Either monads
as match; (3) State as a state passed and returned; (4) hs1003's test
inputs for function arguments and `==` on the module's own types.

Fusing turned out unneeded: Bend takes a type parameter that is a type
function (`-F: Data -> Data`), so `Fix`, `Cofree` and `CofreeF` are one
generic type each (`HsPrelude.bend`, written next to the modules), with the
functor written as `(r_ => G<A, r_>)`; Bend sees a def recurse through
`Fix.Fix{y}` then a match on `y` shrink, also through a field of another
functor (`StuckExprB{BasicExprF<..>}`). It does not see it through a
template, so `G.cata` is written as nested matches, not as an fmap. The
fold now writes those types, `Fix`, `:<` (both), `unFix`, `Base t a`,
`project`/`embed` at Fix and Cofree, and `cata` as the functor's generated
`G.cata` or `G.cata.cofree`, for each data type with a Functor instance
whose fields are copied, recursed into, a Maybe or pair of those, or
another flat functor of the package (one level). A type whose own type
appears at a field (a container such as hs1003's `PQ p a`) gets none.

| telomare library (run/telomare/law-pk4, 49 s) | functions | types | generated | out |
|---|---|---|---|---|
| before (law-pk2) | 82 (55 with laws) | 67 | 0 | 755 |
| now | 90 (55 with laws) | 82 | 44 (22 functors' cata, cata.cofree) | 732 |

hs1003 (run/law8): the same ledger as law7, line for line.

What this does not free yet, and why: telomare's 46 pattern synonyms are
all class-polymorphic (`PairB :: (Recursive g, Base g ~ f, BasicBase f) =>
..`, view patterns through `extractB`, `project`), so inlining one needs the
instance chosen at its type (BasicBase StuckExprF's `extractB = \case
StuckExprB x -> Just x; _ -> Nothing`) and the view pattern turned back
into the constructor it inverts; the same specialisation frees the
class-polymorphic functions (`varB`, `b2i`, `convertBasic`). A functor-
polymorphic function without classes (`rewriteOuterTag :: anno -> Cofree
a anno -> ..`) needs its variable's kind (Data -> Data), which hs-export
does not write yet. GHC's example laws have no LawSx for Fix and Cofree
yet (`nolaw:result-type:Data.Fix.Fix`). A data type with a function field
(Desugar's `Builtin`) is Type, not Data, in Bend.

## Telomare's rules, 2: Maybe and Either as monads (2026-11-19)

GHC writes a do block as its >>= and >> (FORMAT: `expanded stmt`), so the
survey now judges a do block by those methods at their monad (it said
`monad:do` for every one), and the fold writes, at Maybe, Either e and
lists: `>>=` as Base's `Maybe.bind` or the prelude's `hs.either.bind` with
the continuation a closure, `>>` the same with `_ =>`, `return`/`pure` as
`Some`/`Inr`/a one-element list, `fmap`/`<$>` as `Maybe.map`,
`hs.either.map` or `hs.map`, `maybe`, `either` (prelude) and `fromMaybe`
(`Maybe.default`), and `<>` at a list as `List.append`. A bind whose
pattern is a constructor, or a continuation with a let or a case inside,
is still out (a lambda in Bend is one expression).

| | functions out | ok-law | ok-check |
|---|---|---|---|
| hs1003 before (law8) | 3190 | 1360 | 202 |
| hs1003 now (law9) | 3174 | 1373 | 205 |
| telomare before (law-pk4) | 732 | 55 | 35 |
| telomare now (law-pk5) | 727 | 60 | 35 |

No def lost its verdict on either. In telomare the five are all `<>` on
strings (renderMeter, renderBinding, renderDef, indent, plural); its
Maybe/Either code is also blocked by other rules (case on a computed
value, local functions, pattern synonyms).

## Telomare's rules, 3: State, and lifting (2026-11-19)

State before the rest of rule 1, because the class-specialised code rule 1
would free (`convertBasic` over any monad) is mostly State or Either code.
Rules 2 and 3 met the same wall, which this rule takes down too: Bend
matches only parameters and pattern fields (not a let-bound local, not a
computed value), refuses a match after a local statement, and a lambda in
Bend is one expression.

**State.** `State s a` (and `StateT s Identity a`, lazy or strict) is a
function of the state to a result and the next state, `S -> A & S`, an `&1`
pair so the result may be a function (`<*>` carries one). `State s`
alone, a monad argument of `>>=`, is the marker `hs.State<S>`. The
prelude's `hs.state.*` (written into a module that uses one) are `>>=`,
`>>`, `pure`/`return`, `fmap`, `<*>`, mtl's MonadState `get`, `put`,
`modify`, `modify'` and `gets` at State, and transformers' `evalState`,
`execState` and `runState` (the last gives back a Haskell pair, `&2`). A
synonym used with more arguments than it has (`type M = State Meter`, used
as `M ()`) applies its right-hand side to the rest. `ExceptT e (State s)`
(telomare's EALM) is not State: still out.

**Lifting.** These become defs of their own: a case on a computed value or
in an argument, a lambda whose body is a let or a case or whose patterns
are not all variables, a local value whose body is one, a case after a let
(a record update, GHC's `let f' = .. in case r of C .. -> C ..`, is one),
and every where- or let-bound function, one that calls itself too (a rec
group of one). The fold writes a marker (`%lift`, `%ldef`) that carries
the clauses, the result type, the locals in scope with the types GHC gave
their binders (FORMAT's `bv`, `fun`, `export`), and the enclosing def's
type variables; `fd.def.of` takes the markers out. A lifted def is
`NAME.lK` or `NAME.go` for a local `go`; its parameters are the type
variables, the locals its body uses once its own markers are out and the
local functions it calls are calls of their defs, then its own. Each use
of a local function becomes a call of its def with those locals first
(eta-expanded when it has fewer arguments). The ledger says `ok-gen`; Law
skips them (dotted) and counts as laws only `NAME.exK`; a lifted def whose
parent is out goes with it, and a parent whose lifted def fails takes that
failure as its reason.

Not yet: a lifted body that calls the def it came from (the two are
mutually recursive, which Bend refuses: both out); a local function passed
where a template is wanted (`map go xs`, `hs.map`'s `~f`) when it uses a
local that is not a parameter (`fold:closure-argument`); a polymorphic
local (its own type variables); mutually recursive locals; a list of State
actions (`[State Int String]`: a function is Type, a list's element Data).

| | functions out | ok-law | ok-check |
|---|---|---|---|
| hs1003 before (law9) | 3174 | 1373 | 205 |
| hs1003 now (law12) | 3129 | 1403 | 220 |
| telomare before (law-pk5) | 727 | 60 | 35 |
| telomare now (law-pk7, 37 s) | 721 | 61 | 40 |

No def lost its verdict or a law on either. hs1003's 45 are the lifted
cases, lambdas and local functions; the top reasons left are `==` on the
module's own types (94, the next rule), Double (41), sections (27) and
Base functions the fold does not write yet (flip 27, lookup 13, snd 13,
toUpper 12, fst 12, dropWhile 11). Telomare's six: `step` and `built`
(State Meter, `modify'` with a record update), `indentWithOneChild'` and
`indentWithTwoChildren'` (State Int String), `approxBody` (a local
function) and `localDef` (a case after a let, with laws). Its remaining
out are still mostly the survey's (547: classes over the base functors,
Data.Map, ExceptT, pattern synonyms).

## hs1003's rule: `==` at the module's own types (2026-11-19)

The first reason left after rule 3 was `fold:eq-at-type` (94 defs): `==`,
`/=`, `<`, `compare`... at a type Base has none for. Of the 94, 21 were
`==` at a type of the module, 21 at a list (a String, a list of the
module's type), 52 at a type variable (an `Eq a =>` or `Ord a =>` def), and
38 of all of them an order, not `==`.

**`==`.** At a list, Maybe, Either, a pair, `()` and Ordering, the
prelude's `hs.eq.*`, templates given `==` at the parts (`hs.eq.list(~A, ~eq,
xs, ys)`); `==` at the parts is a def's name when there is one (`Nat.is_eq`,
`Char.is_eq`, `T.eq`), else a closed lambda. At a type of the module whose
Eq instance GHC derived (the instance's `$c==` binding is `generated`),
`T.eq`, written from the type's item: a match on both arguments, the same
constructor and `==` at each field, `False` for two constructors; with
parameters, a template taking `~A` and `~eq_A: A -> A -> Bool` for each,
which a recursive field calls with its own arguments (so the template's
copies stay finite). `elem` at such a type is `List.contains`. Out: a
hand-written instance (`fold:eq-instance`: its `==` is not translated yet), a
type nested in a list or a Maybe of its own (`fold:eq-nested`: Bend sees
no decreasing call through a template argument), two types calling each
other's (`fold:eq-mutual`), an earlier module's type whose T.eq is out
(`fold:eq-imported:NAME`, telomare's `LocTag`, nested in its own Maybe).
A T.eq out that nothing calls leaves no row.

**Law** took every dotted name for a law or a def lifted out of a
function: a refused `T.eq` took its type out with it (law:), and its def
was pruned as a law whose def is gone. A dotted name whose first letter is
a capital is now the type's own def.

| | functions out | ok-law | ok-check |
|---|---|---|---|
| hs1003 before (law12) | 3129 | 1403 | 220 |
| hs1003 now (law15) | 3107 | 1424 | 221 |
| telomare before (law-pk7) | 721 | 61 | 40 |
| telomare now (law-pk9, 53 s) | 721 | 61 | 40 |

No def lost its verdict or a law on either; every row of law12 is in
law15. hs1003's 22: `==` at lists and Strings (palindromes), at the
module's enumerations and records, `elem` at them. Telomare's `==` are in
code the survey still refuses or at its `LocTag`. Left of the 94: an
order (`fold:ord-at-type`, 38) and `==` at a type variable
(`fold:eq-at-tyvar`, 31): the dictionaries, next (an `Eq a`/`Ord a` def
takes `~eq_A`/`~cmp_A`, its callers pass `==`/`compare` at their type).

## Telomare's rules, 4: ExceptT over State (2026-11-20)

The user: "Telomare's blockers: ExceptT first, then Data.Map, classes and
pattern synonyms."

**ExceptT.** `ExceptT e m a` is its newtype's `m (Either e a)`. Over
`State s` (or `StateT s Identity`), telomare's three monads (EAL's `EALM`,
IC's `ICM`, Fast's `EvalM`), it is a State whose result is an Either,
`S -> Either E A & S`, so `runExceptT` is the term itself; over Identity
it is `Either e` (the Either monad). `ExceptT e (State s)` alone, a monad
argument, is the marker `hs.ExceptS<E, S>` (a synonym's use, `EALM a`,
applies it). The prelude's `hs.exs.*` (written into a module that uses
one): `>>=` (a `Left` stops the rest, the state it had goes on), `>>`,
`pure`, `fmap`, mtl's MonadState methods lifted through ExceptT (`get`,
`put`, `modify`, `modify'`, `gets`) and MonadError's `throwError` (at
Either too: `Left`).

**Control.Monad.** At State and at ExceptT over State, `mapM_`/`forM_`,
`mapM`/`forM`/`traverse` at a list and `foldM` are the prelude's
`hs.state.*`/`hs.exs.*` `mapm_`, `mapm` and `foldm`, structural on the
list, the function a template (`~f`, so a closed one: a lambda that uses
a local is `fold:closure-argument`, as at `map`). At State, ExceptT over
State, Maybe and Either, `when` and `unless` are an if whose other branch
is `pure ()`, `void` an fmap, `=<<` a `>>=` and `*>` a `>>`. The survey
no longer counts these eight as IO. Out: `<*>` at ExceptT (an Either of a
function is not Data), ExceptT over any other monad
(`fold:exceptt-type`), `catchError`, `withExceptT`, `lift`.

**Test** (`tests/hs/Exc.hs`, 23 functions on ExceptT String (State Int),
State Int, Maybe and Either): 20 check, 15 of them with laws (GHC's
answers, a `Left` with the state it stopped at among them), 5 ok-check
(their result is a monadic action: no law); out `peek` (an `if` in an
argument, `fold:if-in-argument`) and `half` (`even`), and `halfR` with it.

| | functions out | ok-law | ok-check |
|---|---|---|---|
| hs1003 before (law15) | 3107 | 1424 | 221 |
| hs1003 now (law16) | 3107 | 1424 | 221 |
| telomare before (law-pk9) | 721 | 61 | 40 |
| telomare now (law-pk10, 39 s) | 721 | 61 | 40 |

Nothing moved on either, as the survey predicted: hs1003 has no ExceptT
(3 out reasons changed, `traverse` at another monad now
`fold:monad-at-type`), and every one of telomare's 119 ExceptT bindings
is out for something else too. With ExceptT's 110 `type:ExceptT` and its
methods gone from the survey (run/telomare survey, sv1), what those 119
still meet, besides calls: `EALState` (62: Map fields, one keyed by
`Digest SHA256`), EALError (62: a `Digest SHA256` field), `Map` (58),
`Digest`/`SHA256` (38), `ICState` (37: IntMap, Seq, Map, a Digest-keyed
Map), EAL's `Tag` (32), `BodyTemplate` and `ApplySite` (20 each), mutual
recursion (18), Set (17), IntMap (16), Seq (13), Fast's `FastMeter` (12:
a Map field), `int-sub` (7). `Digest SHA256` (crypton's hash of a term's
`encode . show`) is in both EAL's state and its error type, so EAL and IC
stay out until there is a rule for it, whatever Data.Map does. Of the
147 bindings Data.Map, Set or IntMap keeps out, 5 have no other reason of
their own (Levels' `renderLevels`, Resolve's `qualifyBindings`, Size's
`locateSizingFailure`, IC's `icEvalIC`, Fast's `ownerMap`).

## Telomare's rules, 5: Data.Map, Data.Set, IntMap and IntSet (2026-11-20)

**The types.** `Map k v` is HsPrelude's `HsMap<K, V>` (`HsMap.Tip{}`,
`HsMap.Bin{key, val, rest}`), its pairs in ascending order of the key, each
key once; `Set k` is `HsSet<K>` the same way; `IntMap v` is
`HsMap<Nat, V>` and `IntSet` `HsSet<Nat>` (IntSet's `Key` is Int). One
term per map, so `==` at them (`HsMap.eq`, `HsSet.eq`) is the derived one,
and a type whose fields are Maps derives its `T.eq` too. They are their own
types, not lists, so `<>` at them is `union` and not `++`.

**The functions** (HsPrelude, structural on the list; Data.Map's semantics,
a list's cost): the 31 of Data.Map that telomare and the test use, at
Data.Map(.Strict) and at Data.IntMap(.Strict), and 18 of Data.Set and
Data.IntSet (README, Containers). Each takes compare at the key as a
template, written by the fold: `Nat.cmp` at Int, HsPrelude's `HsCmp.char`,
`HsCmp.bool` and `HsCmp.unit`, and `HsCmp.list`, `HsCmp.pair`, `HsCmp.maybe`
given compare at the parts (Haskell's derived Ord: `[]` first, then
lexicographic; `Nothing` first; `False < True`). A function argument
(`insertWith`'s, `map`'s, `filter`'s, `foldr`'s) is a template, so a closed
one. The fold reads which of GHC's type arguments is the key and which the
values from a table per function (`fd.dm.specs.*`, checked against
hs-export's output, `map`'s are `a b k`, `filter`'s `a k`). Out: a key of
another type (`fold:ord-at-type`: the module's own types need their
`compare`, the next rule with the dictionaries), `!` (partial),
`Foldable`'s methods at a Map or a Set, `mempty`, `alter`, `split`,
`mapKeys`.

bend's compiler overflowed its stack on the longer literals (the table as
one list, HsPrelude as one string): both are in pieces now
(`fd.hsprelude.m1`..`m5`, `fd.dm.specs.map1`..).

**Test** (`tests/hs/Mp.hs`, 26 functions on Map Int Int, Map String Int,
Map Char Int, IntMap, Set Int, Set Char, IntSet): 25 check, 24 with laws
(GHC's answers: duplicates, the last one kept, `unionWith`, left-biased
`union` and `<>`, `difference`, `==` at Maps), `build` ok-check (its result
a Map: no law); out `counts` (a list comprehension in an argument,
`fold:do`).

| | functions out | ok-law | ok-check | types |
|---|---|---|---|---|
| hs1003 before (law16) | 3107 | 1424 | 221 | 558 |
| hs1003 now (law17) | 3107 | 1424 | 221 | 558 |
| telomare before (law-pk10) | 721 | 61 | 40 | 82 |
| telomare now (law-pk11, 56 s) | 668 | 64 | 76 | 96 |

hs1003 does not use Data.Map (no row changed). Telomare: 53 out fewer, no
def lost its verdict or a law. They are the records whose fields are Maps
and their selectors (EAL's `CodeGuidance`, `DeferCtx`, `EALResult`, Fast's
`FastMeter`, IC's `Node`, Eval.IC's `ICMeter`, Levels' `LevelsInfo` and
state), Size's functions over them, Size.IR's generated catas, and their
derived `T.eq`s; 36 are ok-check, their result a record or a Map (Law has
no input or answer reader for them yet). Of fold's own reasons left: dep 74,
`Digest` 17, `Rational` 10, `dep:Builtin` 9, `\case` 7; the survey still
refuses 541, most for the classes over the base functors (`Recursive`,
`Corecursive`, `~`, BasicBase, StuckBase), `Void`, ParsecT, EALState's
and EALError's `Digest SHA256`, pattern synonyms, mutual recursion and
`int-sub`.

## Telomare's rules, 6: the specialiser, bend/Spec.bend (2026-11-20)

The user: "/goal have cata be able to get a working version of telomare's
master." Telomare's IR is written for any functor with a class (`BasicBase
f`, `StuckBase f`, ..., with `Recursive g`, `Corecursive g`, `Base g ~ f`)
and read through pattern synonyms over them (`ZeroB`, `PairB`, `BasicEE`,
`GFix`, ... down to views `(extractB -> Just x)` and `(project -> x)`), so
nothing of it was in reach of the fold, which takes no class. Bend has no
classes either; the specialiser takes them out before the fold, as GHC's
specialiser would, on hs-export's output (a pass from export to export, so
survey, fold and law are unchanged):

- **Pattern synonyms.** hs-export exports each synonym's matcher `$mX`
  (GHC's code: a case on the scrutinee whose first match is the synonym's
  pattern, its continuation applied to the pattern's variables) and its
  builder `$bX`. A use as a pattern becomes that pattern, the use's
  arguments in the variables' places and its types in the synonym's; as an
  expression, a call of the builder. Repeated until none is left.
- **Views.** `(f -> p)` becomes a plain pattern when f is the identity, a
  constructor (`Just`, `pure` at Maybe), a one-clause lambda projecting a
  field (`\(_ :< x) -> x`), a function by cases that is `Just x` at one
  constructor and `Nothing` elsewhere (telomare's `extractB = \case
  CompiledExprB x -> Just x; _ -> Nothing`), Recursive's `project` or
  Corecursive's `embed` at Fix or Cofree, a composition of these, or a
  method whose instance (found from the types) defines it as one of these.
  So `PairB a b` at `Fix CompiledExprF` is `Fix (CompiledExprB (PairSF a
  b))`.
- **Dictionaries.** A call of a def that takes dictionaries, at types with
  no variable left, becomes a call of a copy at those types
  (`NAME__TYPES`, its foralls and contexts gone, its recursive references
  the copy's), written into the module that calls it; a method at such
  types whose instance the package wrote by hand (not GHC's derived ones,
  left to the fold), a call of a copy of the instance's method. The
  instance is found from the types, never from the evidence: the
  package's instance heads matched against them, after the package's
  synonyms and type family instances (hs-export now exports these:
  `(faminst ...)`) and recursion-schemes' `Base` at Fix and Cofree are
  applied. Each copy is specialised in turn; a module asks for each copy
  once.
- `f = \case ...` (and `f = \x -> ...`) whose only clause is bare becomes
  f's clauses, which the survey and the fold read parameters off.

Bend computes a call's arguments first, so a branch of `Bool.pick` is
never lazy: every recursion branches on a mode its caller computes (the
first cut took 30 minutes on one module; telomare's 29 now take 26 s).

**Test** (`tests/hs/Cls.hs`: a class, two instances, one at `CofreeF f
Int` with a context, five pattern synonyms with views, constrained
functions at `Fix` and `Cofree`, a class at lists with an instance
context): every copy checks; `sizeFix`, `sizeTagged` (through the Cofree
instance) and `prettyBools` have laws, GHC's answers.

**Telomare** (the export with faminsts; spec 26 s; fold-v1): 668 copies
(350 ok, 12 ok-gen, 306 out) in 18 modules; telomare's own functions
681 out (were 688): `sizingBudget`, `allDataShape`, `describeTau`,
`getLowerBound`, `isForcedZero`, `expansionErrorLoc`, `truncateV`. The
copies' blockers next: mutual recursion (44), Traversable's `sequence`
(39: the instance gives only `traverse`, base's default does the rest),
`show` (27), Applicative at types the fold has no monad for (34),
`error` (13), Machine's `debugTrace` (13), `CarryWrap` left unapplied (13).

Then (same day): hs-export gives each instance line its class's variables,
methods and superclass count, so base classes' instances (Applicative,
Traversable, ...) resolve too; a family instance applies to more arguments
than its own (`CarryWrap g g`); Traversable's `sequence`, `sequenceA` and
`mapM`, when the instance takes base's default (GHC's `$csequence =
$dmsequence ..`), are `traverse` (sequence given `id`); `f x = \case ..`
becomes clauses with x first. Telomare (spec 29 s): copies 410 ok, 12
ok-gen, 329 out; its own functions 148 ok (were 140 before the
specialiser), no def lost its verdict.

What telomare's own functions wait on now (survey of the specialised
export, those taking no class): Digest SHA256 in EAL's state and error
(EALError 67, EALM 61, EALState 60, Digest 59, ICState 39), megaparsec
(TelomareParser 60, ParsecT 57 and its methods), mutual recursion (48),
non-structural recursion (33), Int with negative numbers or subtraction
(27: telomare's function indices are negative, `leftGateInd = -2`), EAL's
`Tag` (31), Data.Binary's Get/Put/Word8 (Artifact), Data.Sequence (12),
Rational (10); the copies on `error` (16), `show` at Fix (12, data-fix's
instance through Show1), Applicative at Identity, Either and pairs
(liftA2), and the fold's `\case` inside expressions.

## Telomare's rules, 7: signed Int, Identity, liftA2 (2026-11-20)

The user: "/goal have cata be able to generate a working version of
telomare's master."

**Int.** Telomare's Ints go below zero (its function indices: `leftGateInd =
-2`), so Int as Nat, where nothing subtracts, cannot hold it. In the
specialiser's output `Int` is HsPrelude's `HsInt` and `Integer` its
`HsInteger` (the same type to the fold; Law tells them apart for GHCi):
`Pos{n}` is n, `Neg{n}` is -n with n at least 1, so each integer is one
term and `==` is the structural one. HsPrelude gives `add`, `sub`, `mul`,
`negate`, `abs`, `signum`, Haskell's `div`/`mod` (toward minus infinity)
and `quot`/`rem` (toward zero), `^`, `cmp` and the comparisons, `max`,
`min`, `succ`, `pred`, `show`, `range`; the fold writes literals and
literal patterns below zero, `(negapp ..)`, `-`, `subtract`, `negate`,
`abs`, `signum`, `fromIntegral` and `toInteger` between Int and Integer,
`toEnum`/`fromEnum` at Int, and `compare` at HsInt for a Map's key.
`IntMap v` is `Map HsInt v`, `IntSet` `Set HsInt`, their functions Data.Map's
and Data.Set's with HsInt as the key's type argument. Law gives HsInt
inputs below zero too (0, 1, -1, 2, -3) and reads a number answer as an
HsInt where the def's result type has one. Not modelled: Int's 64-bit
wrap-around. A single module (hs1003) keeps Int as Nat.

**Identity** (`Identity a` is `a`: the newtype erased; `Identity` and
`runIdentity` are `id`) is a monad to the fold; **liftA2** at Identity, Maybe,
Either, State and ExceptT over State is `x >>= \la_ -> fmap (f la_) y`
(Identity: `f x y`).

**Test** (`tests/hs/Ints.hs`): 9 of 11 with laws (negative inputs and
answers among them: `sign (-1) == -10`, `div`/`mod`/`quot`/`rem` below
zero, IntMap and IntSet at negative keys); out `divs` (a 4-tuple) and
`countDown` (recursion on n - 1, not structural).

## Telomare's rules, 8: Digest SHA256 (2026-11-20)

EAL's state, its error type and its `Tag` all hold crypton's `Digest
SHA256` (the hash of a defer body's `encode . show`, a body's identity in
the DeferMap), so no rule before this one could reach EAL or IC. In the
specialiser's output a `Digest SHA256` is HsPrelude's `HsDigest`, its 32
bytes; `hash` is SHA-256 (FIPS 180-4) in Bend, on U32 words (Base's `add`,
`and`, `xor`, `not`, `shrn`, `shln`); `show` is its hex text (crypton's,
no quotes); `==` and `compare` its bytes' lexicographic order (crypton's
Ord); `SHA256` itself, the algorithm's tag, is `()`. A ByteString (strict
or lazy) is a list of `Word8`, which is Bend's U32 (its wrap-around at 256
not modelled); `pack`, `unpack`, `toStrict`, `fromStrict` are the list;
Data.ByteArray's `unpack` at a digest its bytes; utf8-string's `encode`
UTF-8 (one to four bytes); `fromIntegral` from Word8 to Int or Nat.

Checked against GHC: `tests/hs/Dig.hs`, `show (hash ..)`, `==`, `compare`
and the first bytes of digests of GHC's inputs, 4 functions with laws
(the empty string's digest among them, e3b0c442..); and the FIPS vectors
("abc", "", the 448-bit one) and UTF-8 text of 2, 3 and 4 bytes against
sha256sum.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare before rule 6 (law-pk11) | 668 | 64 | 76 | 96 |
| telomare after rules 6-8 (spec, law7, 61 s) | 573 | 80 | 142 | 109 |
| hs1003 before (law17) | 3107 | 1424 | 221 | 558 |
| hs1003 now (law19) | 3090 | 1427 | 232 | 561 |

No def lost its verdict or a law on either. Telomare's numbers are its
own functions; besides them the specialiser's 738 copies (464 check, no
laws: GHC has no copy to answer for).

## Telomare's rules, 9: base's list functions, Bifunctor, Seq, coerce (2026-11-20)

The survey passed base's list functions (`zip`, `fst`, `lookup`, ...) that
the fold had no rule for, so a def using one was out at the fold
(`base:...`), not at the survey. They are HsPrelude's `HsList` now (see
README, Lists), with `==`/`compare` at the element as templates and the
fold's table naming the roles of GHC's type arguments (`fd.dm`, as for
Data.Map). Foldable at Set and Map (their elements, their values), `fmap`
at Map, `mempty`, Data.Bifunctor at Either and pairs, `flip`, `trace`,
`liftM2`, `<*>` at Maybe, Either and ExceptT over State, Data.Sequence (a
list), `zip [n ..]` (the specialiser's rewrite to HsList's `zipFrom` and
the like), and `coerce`: a newtype's derived instance (Enum at
`FunctionIndex` and `UnsizedRecursionToken`, which 124 of telomare's
functions reached) is coerce of the field type's, so the specialiser
copies it like a hand-written instance and the fold writes coerce with
the newtype's constructor and selector.

The gate: an error inside a template's instance (`Location: List.foldr~0`,
its lines Base's) named no line of the file, so the gate blamed the last
item, then the next, until the culprit went: every def after it was out
with its error. It blames the item of the file's K-th call of the
template's def now (when that is an item). foldr and foldl are HsList's,
whose element the function may copy (Base's take it once).

**Tests**: `tests/hs/Lists.hs`, 28 functions, 19 with laws (GHC agrees),
the rest check (their arguments or answers are Maps or Sets, which the
laws do not read yet); `tests/hs/Newtypes.hs`, succ, toEnum and fromEnum
of derived Enum at newtypes with laws (a newtype without a field name:
out, `fold:coerce-at-type`).

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rules 6-8 (law7) | 573 | 80 | 142 | 109 |
| telomare after rule 9 (spec6, law10, 88 s) | 539 | 85 | 170 | 110 |
| hs1003 after rule 8 (law19) | 3090 | 1427 | 232 | 561 |
| hs1003 after rule 9 (law20) | 3027 | 1512 | 244 | 561 |

No def lost its verdict on either. Telomare's copies: 537 check (464).
What still blocks telomare's own functions, by the survey: recursion Bend
does not take (mutual 96, non-structural, `error` and `!!`), megaparsec
(the parser), Data.Binary's Get and Put, `show` at its types (and at Fix
through Show1), `Rational`, `Int64`, `iterate`.

## Telomare's rules, 10: Show at base's types (2026-11-20)

`show`, `shows` and `showsPrec` at Int, Char, String, Bool, (), lists and
Maybe are HsPrelude's `HsShow`, GHC.Show's text (a negative Int in
parentheses above precedence 6; Char and String with GHC's escapes, `\&`
where a digit or `H` follows a numeric or `\SO` escape). `ShowS` is a
type (String -> String). GHC's derived `showsPrec` of the package's own
types is copied at its type like a hand-written instance: its bare Int
literals (`showParen (a >= 11)`, `showsPrec 11 b1`) the specialiser makes
HsInt literals, and base's default `show` and `showList` given it are
HsPrelude.Z's `showVia` and `showListVia`.

The index: a type and its constructor may share a key (`data T = T ..`);
a value's lookup skips the types and a type's takes only them
(`fd.ix.findv`).

**Tests**: `tests/hs/Shows.hs`: 13 with laws (GHC agrees), 5 derived
`showsPrec` check (a ShowS answer, which the laws do not read), `shapes`
(show at a list of the file's own type) out, `fold:show-at-type`.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 10 (spec8, law13, 95 s) | 538 | 85 | 171 | 110 |
| hs1003 after rule 10 (law22) | 3023 | 1515 | 245 | 561 |

No def lost its verdict on either. Telomare's copies: 595 check (537).
Show still blocks most of telomare's: its types' Show instances call the
imported ones (SourceSpan, UnsizedRecursionToken), Show at Fix is
through Show1 (mutual), and its pretty printer (PrettyPrintable) is
mutual.

## Telomare's rules, 11: recursion Bend refuses, with fuel (2026-11-20)

The user: "What still blocks telomare's own functions: our bend branch of
telomare should signal you how to approach these. Do not use unsafe."

The bend branch writes each recursion Bend refuses with a Nat fuel, none
with `@unsafe`: Desugar.bend's `go(+fuel, scope, n: ON) -> OV` is master's
mutually recursive walks over terms, patterns, their lists and bindings as
one def of a sum (`ON`: OT, OP, OTs, OBs, OAs, OArgs, OSpine) answering a
sum (`OV`, taken apart by `vt`, `vp`, ... with a default at the others),
`fuel()` = `U32.to_nat(4294967295)`, at 0 a default (`VT{S.SZero{..}}`);
Levels.bend's `occ` the same with one answer type; Expand, Resolve, Size,
EAL, Mega and Parse likewise. The fold now writes them so (README,
"Recursion Bend refuses: fuel"):

- the gate reads Bend's "a decreasing self-call" and, when a default of
  the def's type is to hand, writes the def as `f.fu` (the fuel after its
  type and template parameters) and `f` (from 2^32 - 1) instead of taking
  it out; Bend's own check decides which defs need it, so a def Bend sees
  shrink keeps its structural recursion;
- before the gate, each cycle of calls among the module's defs (two or
  more, found by reachability) whose members take no type or template
  parameters and fold whole is one def `HEAD.mu` over `HEAD.mu.In`, its
  answer the members' or `HEAD.mu.Out`;
- defaults: Base's and HsPrelude's types, pairs, Either, Fix, Cofree, and
  data types, the module's or (in a package) the modules' before it, now
  handed on in the package (`Px`'s `dt`, the types as a later module
  names them);
- the survey no longer puts a def out for `nonstructural` or `mutual`
  (both are its notes now); `rec-value` stays a reason (a function value:
  Bend's templates take only closed arguments, and `f.fu(p)` is not);
- the specialiser writes `f $ x` as `f x` and `(f . g) x` as `f (g x)`
  (`f` passed to `$` was a use as a value: rec-value 57 -> 44 in the
  survey of telomare).

**Test** (`tests/hs/Fuel.hs`): `halvings`, `digits`, `gcd'` (no argument
shrinks), `isEven`/`isOdd`, `sizeR`/`sizeF` (a rose tree through its
list), `render`/`renderAll` (a String and a [String]: the Out sum) with
laws, GHC agrees: 16 ok-law, 3 types; out: `collatz` (base's `even`),
`build` (a let in an expression), `range` (build's).

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 10 (law13) | 538 | 85 | 171 | 110 |
| telomare after rule 11 (spec9, law19, 224 s) | 536 | 87 | 171 | 110 |
| hs1003 after rule 10 (law22) | 3023 | 1515 | 245 | 561 |
| hs1003 after rule 11 (law24) | 2969 | 1559 | 255 | 561 |

No def lost its verdict on either. Telomare's copies: 611 check (595).
Newly in: `indentation`, `decendant`, derived Show of EAL's Tau, Sigma
and CapShape (a mutual group) and IR.Types' DataType, Size's `intB` (a
default of another module's type), `unsizedStepBody`, copies of `i2B`,
`s2b`, `deferS` and `bLamAFP`. The survey of telomare's own functions:
449 -> 447 out (467 before rule 11). Most of its mutual and
non-structural recursion is waiting on something else as well: the
parser (megaparsec, TelomareParser), the pretty printers' Show at Fix
through Show1 (now the sole blocker of 30), view patterns (100 affected),
Applicative at a type variable (103), `error` (83), `!!`.

## Telomare's rules, 12: type arguments, as-patterns, `\case`, `<*>` chains (2026-11-20)

The goal stands ("have cata be able to generate a working version of
telomare's master"). Measured from the pipeline's roots
(`Driver.compileModules`, `evalLoopCore`, `Fast.compileFast`,
`runFastLoop`), 316 of telomare's functions they reach were out in the
survey; the four rules here are what stood between the survey and the
fold, or between the fold and Bend's check:

- **Type arguments normal** (Spec): every `tyapp`'s type has the
  package's synonyms expanded and families applied. `cata` at `Term3`,
  `BasicExpr`, `PatternA`, `UnsizedExpr`... (synonyms of Fix and Cofree)
  was `method:Recursive.cata@Term3` to the survey; it is cata at Cofree
  now. The pipeline's closure: 316 -> 309 out.
- **As-patterns** (Spec): a clause's `x@p` is `p`, its wildcards named
  (`as_wPATH`), and each use of `x` in the clause the term `p` builds
  (the constructor at the pattern's types applied to its fields, a tuple,
  a list, a literal). A clause whose as-pattern holds a record pattern, a
  negative literal or a view is left as it was (`fold:pattern-pas`); so is
  one in a do or list-comprehension bind. Telomare's export had 235.
- **`\case` and `\cases` in an expression** (Fold): a lambda by cases,
  lifted like any lambda whose patterns are not all variables (it was
  `fold:lambda-case`: `b2v = cata $ \case ..`).
- **`<*>` after `<$>`** (Fold): `g <$> y <*> x` is `y >>= \v -> fmap (g v)
  x`, `(y >>= \v -> e) <*> x` is `y >>= \v -> (e <*> x)` and `pure g <*>
  x` is `fmap g x`, at Maybe, Either and ExceptT over State. The old
  `f >>= \g -> fmap g x` put a function inside a Maybe, which Bend refuses
  (a function is Type, a Maybe's part Data): 27 of telomare's defs failed
  Bend's check so (`b2s`, `cshowP1__*`, `checks`).
- `sum` and `product` at Int and Integer (HsInt).

**Tests**: `tests/hs/LamCase.hs` (all 9 in: 6 laws, 3 check),
`tests/hs/As.hs` (as-patterns in clauses, nested, in a case, under a
tuple, a list and a char literal: 8 laws; `pick` waits on a guard that
falls through, `heads` on a list comprehension), `tests/hs/Ap.hs` (7 laws,
were 5 check failures), `tests/hs/Lifted.hs` (a where-function that calls
its def: a cycle, rule 11's `.mu`; 2 laws). Fuel, Shows, Nt and Help
unchanged.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 11 (spec9, law19) | 536 | 87 | 171 | 110 |
| telomare after rule 12 (spec11, law22, 281 s) | 519 | 88 | 187 | 110 |
| hs1003 after rule 11 (law24) | 2969 | 1559 | 255 | 561 |
| hs1003 after rule 12 (law26) | 2959 | 1569 | 255 | 561 |

No def lost its verdict on either (hs1003 does not go through the
specialiser, so it sees the fold's two). Telomare's copies: 628 check
(611), 225 out (242).

What the pipeline's closure waits on now (309 out, survey of spec11):
megaparsec (TelomareParser 56, ParsecT 55 and its methods: Parse's 60),
`error` (17), EAL's simplex over Rational (Rational 10, Tab 7, Row 5,
Data.Graph), view patterns (11), `!!` and `iterate` (8, 7), Show at Fix
(8), ReaderT (6), a function passed as a value that is the def itself or
its group (`rec-value`, 24: `parent >>= locStartLineColumn`, `foldMap
refsOf x`, `maybe (pure t) walkTau`, `tag anno <$> project x`), IO
(`evalLoopCore`, `runFastLoop`). The fold's own gaps there: local pattern
bindings (`let (r, (m, _)) = ..`, 7), sections (9), `let`/`if` in an
argument (7), Show at a Maybe of the module's own type (`cshowsPrec__LocTag`,
11 copies), a guard that falls through to the next clause.

Next: specialise a call at a known function argument (rec-value and
closures; `tests/hs/RecV.hs`'s shapes), then `error`.

## Telomare's rules, 13: a def's own name as a value (2026-11-20)

Goal: the recursion telomare writes through a function value (`parent >>=
locStartLineColumn`, `foldMap refsOf x`, `maybe False go (lookup h m)`)
reaching Bend as a call of the def, which the survey and the fold take.

- **Recursive references as values, eta-expanded** (Spec, `sp.p9`): a
  reference to a recursive def (`(self X)`, or X by its global name inside
  its own group) that is not applied to all its parameters is the lambda
  `\eta_0 .. eta_m -> X a1 .. ak eta_0 .. eta_m`, the binders' types
  X's. A reference called with all its arguments is kept. Survey rows
  `rec-value:NAME` on telomare's export: 44 -> 16.

**Tests**: `tests/hs/RecV.hs`: `startOf` (`parent >>= startOf`) in, 5
laws. `refsOf`, `tagsOf` now wait on foldMap at a derived Foldable,
`hasRef` on any at it, `double` on fmap at a derived Functor, `settle` on
a monadic value that recurs (no parameters to eta-expand). LamCase, As,
Ap, Lifted, Fuel, Shows, Nt and Help: no losses (As +2 ok-law, `pick` and
`tags`, against a ledger from before rule 12's fold: rule 12's, not this one's).

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 12 (spec11, law22) | 519 | 88 | 187 | 110 |
| telomare after rule 13 (spec12, law22, 272 s) | 502 | 95 | 197 | 110 |

No def lost its verdict (12 out -> ok-check, 7 out -> ok-law); copies
630 check (628), 223 out (225). hs1003 does not go through the
specialiser: unchanged (2959 out).

The pipeline's closure: 309 -> 283 out. The 16 `rec-value` left are
values with no parameters that recur (`getShape :: Get Shape`,
`presolve`, `reduce`, `resolveApplies`, `settle`) and local `go`/`f`
passed as values (`optimizeBuiltinFunctions`, `isUnbounded`,
`validateVariables`).

Next: a value that recurs, by fuel (rule 11's `.fu` with no other
parameter), and local recursive functions as values; then Foldable and
Functor at a derived instance; then `error`.

## Telomare's rules, 14: values that recur, local recursion as values (2026-11-20)

- **A value that recurs** (Survey): a def with no parameters whose body
  names it (`settle = do ..; when (n > 1) (modify (`div` 2) >> settle)`)
  calls itself; it was `rec-value`. The survey says nonstructural and the
  gate gives it rule 11's fuel: `settle.fu(fuel_)`, the default at 0.
- **Local recursive functions as values** (Spec, `sp.p9`): the members of
  a `(rec ..)` group of local bindings are eta-expanded like the
  module's own recursive defs (`maybe False go (lookup h m)`, `(f .
  Set.map ..) $ ..`).
- **Through type and dictionary applications** (Spec): the head of `tag
  @a @anno $dRecursive anno` is `tag`, given one of its two arguments; a
  binder's type is read under its `forall`s and its context.

**Tests**: `tests/hs/RecV.hs`: `settle` in (check: no law at State),
`settleList` 8 laws. The other tests: no change.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 13 (spec12, law22) | 502 | 95 | 197 | 110 |
| telomare after rule 14 (spec13, law23, 294 s) | 501 | 95 | 198 | 110 |
| hs1003 after rule 12 (law26) | 2959 | 1569 | 255 | 561 |
| hs1003 after rule 14 (law27) | 2958 | 1569 | 256 | 561 |

No def lost its verdict. Survey `rec-value` on telomare: 16 -> 0; the
closure 283 -> 281 out. `isUnbounded` is in (check); `tag`, `stuckStep`
and `optimizeBuiltinFunctions` wait on their other reasons (Recursive's
`project` at a type variable, view patterns, `mapScoped`).

Next: what the closure waits on (281): megaparsec (TelomareParser 56,
ParsecT 55 and its methods), then `error` (17).

## Telomare's rules, 15: known function arguments (2026-11-20)

- **Known function arguments** (Spec, `sp.p10`, after `sp.p9`): a call of
  a package def at a function parameter, the argument known (not a local
  variable), at closed types, the def's patterns there variables or
  wildcards, is a call of `NAME__fHASH`: the def with the argument in the
  parameter's place, the argument's free locals its first parameters
  (`fv_i`), dictionary locals left in place. Not copied: a def's own
  self-calls, and inside a copy the def at another argument (no copy
  grows another without end).
- The walk is structural (the first try counted a `Nat` fuel down from
  10^6: `U32.to_nat(1000000)` peeled one at a time costs ~60 s per million,
  and spec hung on every module).
- The package index (`Ix`) has an eighth list, `fns`: the package's defs
  with a function parameter.

**Tests**: `tests/hs/FunArg.hs`: `sumT` (through `mapT sumT`, one `.mu`
with the copy), `sumTs` and `useTwiceL` out -> ok-law; `twice (+ n)`,
`mapI (\x -> a * x + b)`, `go id` copied (check). The other tests: no
change.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 14 (spec13, law23x) | 501 | 95 | 198 | 110 |
| telomare after rule 15 (spec14, law23x, 276 s) | 501 | 95 | 198 | 110 |

No def lost its verdict. On telomare the rule is neutral for now: 14
calls are copied (`putList`/`putMap`/`putMaybe` at Artifact's putters,
`mapScoped`, `projection`, the EAL solvers, `compileReporting`,
`runMainCore`), and the 38 new copies are out for their other reasons
(PutM, Rational, megaparsec, `error`). hs1003 is unchanged (its ledger
does not run the specialiser).

Next: megaparsec at `Parsec Void String` in Bend (HsPrelude), whose
combinators (`many`, `sepBy`, `between`, `choice`) take parsers as
function arguments: this rule's copies.

## Telomare's rules, 16: megaparsec (2026-11-20)

The user's goal: "have cata be able to get a working version of
telomare's master". The closure (what compileModules needs) waited first
on the parser, megaparsec 9.7.0 at `Parsec Void String` (TelomareParser
56 and ParsecT 55 of its 281 out).

- **HsPc** (`prelude/HsPc.bend`, written into HsPrelude.bend): a parser is
  `HsPcSt -> HsPcRep<A>`, the reply megaparsec's four continuations as one
  value; the class methods, `try`, `label`, `hidden`, `lookAhead`,
  `notFollowedBy`, `eof`, tokens, `takeWhileP`/`takeWhile1P`, the Lexer's
  one-shot functions, `charLiteral` (GHC's `readLitChar`), `runParser` and
  `errorBundlePretty`, ported from megaparsec's source. Checked against
  megaparsec on 28 parsers and inputs (`tests/pc/`): every answer and
  every error text the same.
- **The model** (`prelude/Cata/Parsec.hs`, exported with the package):
  what runs a parser again or hands one to a function (`many`, `some`,
  `sepBy`, `sepBy1`, `manyTill`, `skipMany`, `skipSome`, the Lexer's
  `space`, `lineFold`, `indentGuard`, `skipBlockCommentNested`), as
  parser-combinators and megaparsec define them, at `Parsec Void String`.
  Against megaparsec on 4,004 inputs of `tests/hs/Pc.hs`'s grammar: the
  same answers, error texts included. Bend refuses a template that calls
  back its caller, so these are package code instead: rule 15 copies them
  at their known parsers, and the copies join the grammar's group.
- **Spec**: a call of one of those as the model's def (`sp.pc`); `choice`
  at a literal list as `<|>` to `empty`; `uncurry g p` at the model's g
  as `g (fst p) (snd p)`; a parser parameter is a function parameter (the
  index, rule 15); `(\x -> e) a` as `e` with `a` (`sp.beta`: a copy of
  `lineFold` applies its action); a local binding generalised over a type
  and used at one type as the binding at it (`sp.pl`: identifierRaw's
  `where check x = .. fail ..` over its monad); `Parsec e s`, `Token` and
  `Tokens` at String normal; `f $ x` and `(f . g) x` read through
  `(expanded ..)` wrappers, a chain `f . g . h $ x` as `f (g (h x))`.
- **Survey**: ParsecT's types, methods and the functions above; a pattern
  synonym's builder `$bX` is a binding (other modules call it).
- **Fold**: the types (`hs.Pc` the monad's marker, applied by a synonym
  of fewer variables); `MkPc` for `>>=`, `pure`, `fmap`, `<*>` (Apv's
  chains), `<|>`, `empty`, `<*`, `<$`, `fail`; HsPc's table; a def whose
  answer is a parser takes the state last and answers the reply (`fd.eta`:
  a grammar's parsers are a `.mu` of Data answers, no closure run twice);
  a local value that names itself lifted as a def of no parameters (the
  gate fuels it); string literal patterns; `maxBound`/`minBound` and
  `fromInteger` at Int; Data.Char's predicates from GHC's tables
  (`prelude/HsChar.bend`, `tools/char-table/CharTable.hs`); HsPcRep's
  default; a bare `dep` names what it depends on.
- **hs-export**: `run/gcroot-hsx` was a stale build that writes no type
  family instances; telomare is exported again with the current one
  (`run/gcroot-hsx2`, `nix build .#hs-export`), the same files as before
  but for the model's module.

**Test** (`tests/hs/Pc.hs`): a grammar of telomare's shapes (a lexer from
the Lexer, `try`, `<?>`, `choice` over `try`, `sepBy` through brackets,
parsers that call each other, a `lineFold`, `manyTill` at a local
indentation, `let` blocks): `parseE`, `parseOk`, `column`, `mkApp` and
`ex1`..`ex7` ok-law (49 laws against GHC, three of them error messages),
every parser and copy ok-check. The other tests: no change.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 15 (spec14, law23x) | 501 | 95 | 198 | 110 |
| telomare after rule 16 (spec23, law30, 399 s) | 507 | 97 | 239 | 110 |

No def lost its verdict; 41 out -> ok-check, 2 out -> ok-law. The out
count grows by the 37 builders now listed (most need a class of the
package) and the model's 13 defs (those not copied are out: they run a
closure twice). Telomare.Parse: 68 ok-check (the lexer, `identifierRaw`,
`parseSameLvl`, the copies of `many`, `some`, `manyTill`, `space`, the
SourcePos functions), 1 ok-law (`rws`). Its grammar (parseLongExpr and
the 50 parsers around it) is one group that still goes as a whole.

## Telomare's rules, 17: closures to base's folds; the parser runs (2026-11-20)

Rule 16 left telomare's grammar (parseLongExpr and the ~50 parsers that
call it) out as one group. The law's new `OUT/M_drops.tsv` (each item the
gate or the fold dropped, and why; `OUT/M_all.bend`, the items before the
gate) named the root: `parseApplied`'s `foldl (\a b -> x :< embedL (AppF a
b)) f args`, a closure over the pattern's `x` as foldl's template
(`fold:closure-argument`); every other parser of the group went with it.

- **Base's model** (`prelude/Cata/Base.hs`, exported with the package
  before `Cata/Parsec.hs`): `foldr`, `foldl`, `foldl'`, base's
  definitions (foldl's loop takes the list first, so Bend sees it shrink).
  Spec writes a call of Foldable's `foldr`/`foldl`/`foldl'` at a list as a
  call of the model's def at the types after the list (`sp.pc.btab`), when
  the package has the model (`sp.ix.hasbase`); rule 15 then copies it at
  its known function argument, a lambda's free locals the copy's first
  parameters.
- **Fold**: a local's recursive reference (`self (l "go" N)`) is a local,
  not the def's own call: its lifting had passed the def's type
  parameters twice (`foldl.go(~B, ~A, ~f, B, A)(..)`, `many.go(~A, ~p, A,
  ..)`), so a polymorphic def with a recursive `where` failed its check.
  `(f . g) x y` and `(op y) x z` in one spine (a copy's composition in
  its parameter's place, `foldr (PairP . i2B . ord) ZeroB`) are `f (g x)
  y` and `op x y z`, not `fold:section`. `maxBound`/`minBound` at Int are
  2^48 - 1 and -(2^48 - 1), Bend's runtime's largest immediate Nat (GHC's
  2^63 - 1 stopped the run: "a Nat past the largest immediate 2^48-1",
  at `naturalIntRaw`'s range check of every number literal).
- **Check against GHC** (`tests/telomare/run.sh`): runParseModule under
  GHC and in Bend (law37's Bend of the modules through Telomare.Parse) on
  13 files: Prelude.tel, tictactoe.tel, tc_ultra_minimal.tel,
  test/programs' simpleplus.tel and testchar.tel, and 8 malformed inputs
  (`tests/telomare/bad/`): each item's kind, names and spans, and each
  error's text, the same.
- **Test** (`tests/hs/Clo.hs`): foldl at a lambda over a pattern's
  variable, foldr and foldl' over parameters, a fold in a fold's lambda,
  foldl at a def: all 10 ok-law; the model's three defs ok-check. The
  other tests (ap as lc lp fu sh nt t rv fa pc, spec25 + law35): no def
  lost; pc 2 out -> ok-check (`many`'s and `manyTill`'s generic defs, the
  local self-call).

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 16 (spec23, law30) | 507 | 97 | 239 | 110 |
| telomare after rule 17 (spec24, law37, 421 s) | 474 | 97 | 275 | 110 |

No def lost its verdict; 56 out -> ok-check. Telomare.Parse: 117
ok-check, 1 ok-law, 4 out (`commaSep`, `commaSep1`, used only through
their copies, and the test helpers `runTelomareParser`,
`parseSuccessful`, over any monad). What compileModules waits on next
(the survey's frontier over its 219 defs): `error` (17 defs), EAL's
simplex over Rational (Rational 14, Tab 9, Row 8, Elim 4), view patterns
(11), `!!` (8) and Map's `!` (7), `iterate` (7), `show` at Fix (6),
ReaderT (6).

## Telomare's rules, 18: Rational and list comprehensions (2026-11-20)

compileModules' frontier after rule 17 held EAL's simplex over Rational
(Rational 14, Tab 9, Row 8, Elim 4) and, through EAL, 41 list
comprehensions (20 in EAL) that the fold left out (`fold:do`).

- **Rational** (`prelude/HsRational.bend`, written into HsPrelude.bend):
  `HsRational{num: HsInt, den: Nat}` in lowest terms, den at least 1
  (GHC's invariant, so equality is structural); Spec writes `Rational` and
  `Ratio _` as it; Survey takes its Num, Fractional and Show methods and
  `%`; the fold maps `+ - * /`, `negate`/`abs`/`signum`, comparisons,
  `fromInteger` and literals (`frac` as `HsRational.mk`), `fromIntegral`
  from Int, `numerator`, `denominator`, `%`, `gcd`/`lcm` (Int), `show` and
  `showsPrec` (GHC.Real's); Euclid's gcd fuelled by its second argument; a
  zero denominator answers 0 (GHC's error). Twelve answers against GHC's
  (`5 % 6`, `(-15) % 8`, `((-3) % 4)` at precedence 8, lcm 4 (-6) = 12, ...)
  the same.
- **List comprehensions** (Spec's `sp.lc`, before the other passes): the
  report's translation (3.11) to `if`, `let` and `concatMap` of a lambda
  (a wildcard clause when the generator's pattern can fail); the lambda's
  argument type the generator list's element type (a local of known type)
  or the pattern's. `concatMap` joins Base's model (`prelude/Cata/Base.hs`),
  so a lambda over an earlier generator's variables is copied.
- **Test** (`tests/hs/Rat.hs`, with the model): EAL's scaleRow (a
  comprehension over rationals, `foldr (lcm . denominator . snd)`), a pivot
  step, `%`, `/` by a literal, `max`, `show`: 3 ok-law (`ex1` the scaled
  row, `ex3` the shown ratio, `ex5`), the rest ok-check (laws do not write
  a Rational yet: `nolaw:argument-type:HsPrelude.HsRational`). The other
  tests (spec27 + law39): no def lost.

| | out | ok-law | ok-check | types |
|---|---|---|---|---|
| telomare after rule 17 (spec24, law37) | 474 | 97 | 275 | 110 |
| telomare after rule 18 (spec27, law39, 711 s) | 455 | 97 | 292 | 113 |

No def lost its verdict; 20 out -> ok-check, 3 out -> ok-type, 67 new
copies ok-check. Telomare.Parse's 13-file check against GHC still the
same. compileModules' frontier (226 defs, 223 no): Map's partial `!`
(18), `error` (17), view patterns (11), `!!` (8), `iterate` (7), `show`
at Fix (6), ReaderT (6).

## Telomare's rules, 19: view patterns at a class's instance, iterate, Alternative at Maybe, pairs, Kleisli (2026-11-20)

compileModules' frontier after rule 18 (226 defs, 223 no) held, besides the
partial functions (`error`, Map's `!`, `!!`) that wait for the user's
rule, view patterns (11), `iterate` (7), Alternative's `<|>` at Maybe (3),
base's instances at pairs (`pure`, `<*>`, `traverse`, `fmap` at `(,) w`:
9) and Control.Monad's `<=<` and `>=>` (4).

- **View patterns** (Spec's `sp.p3`): a selector's answers are read
  through their casts (an instance with associated types, LamBase's
  `extractL`, casts its `Just x`), and `pure x` at Maybe is `Just x`
  (Term3LiftingF's `extractB`); a method's instance is picked by its
  class's types alone, the method's own may hold variables (EAL's
  `envUsageL`, over the annotation `b`). telomare's tree has 736 view
  patterns after the specialiser before, 688 after; the 11 in
  compileModules' reach are gone, and 10 copies of `extractL`/`extractB`/
  `extractS` (ok-check) are no longer asked for.
- **`iterate f x !! n`** is Base's model's `iterateIndex f x n` (f applied
  n times; a negative n `(!!)`'s error), copied at its known f (rule 15).
  The 7 uses now wait only on the partial-function rule.
- **Alternative at Maybe**: `<|>` is HsPrelude's `hs.maybe.alt` (its second
  argument a thunk, as Haskell's is lazy), `empty` `None`.
- **Pairs**: a Functor, Applicative or Traversable method whose class type
  is `(,) w` is Base's model's (`pairFmap`, `pairPure`, `pairAp`,
  `pairLiftA2`, `pairTraverse`) at w then the method's types, and `g <$> y
  <*> x` there `pairLiftA2 g y x` (no pair holds a function). A copy is at
  w's own Monoid: Resolve's deferLift folds into `(DeferMap, term)`, and its
  traversals' pair copies check (16 ok-check); DeferMap's `<>` itself is
  out (`unionWithKey`, and an `error`).
- **Kleisli**: `<=<` and `>=>` are Base's model's `kleisliR`, `kleisliL`,
  copied at their monad and known functions.
- **Tests** (`tests/hs/Iter.hs`, `Alt.hs`, `Pair.hs`, `Kleisli.hs`, with
  the model): Alt 7 ok-law, Pair 9 ok-law (its `sequence` at a derived
  Traversable stays out, `method:Traversable.sequence@U`), Kleisli 7
  ok-law; Iter's uses wait on `error` (with `iterateIndex` total, all 8
  were ok-law). The other tests (spec31 + law40): no def lost.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 18 (spec27, law39) | 450 | 97 | 282 | 113 |
| after rule 19 (spec31, law40, 784 s) | 446 | 98 | 285 | 113 |

No def lost its verdict. compileModules' frontier: 223 defs, 220 no;
`error` 24 (the `iterateIndex` copies among them), Map's `!` 18, `show` at
Fix 6, ReaderT 5 (a fold into functions), LamBase 4.

## Telomare's rules, 20: ReaderT, CofreeF's instances, derived Functor/Foldable/Traversable, twins (2026-11-20)

Resolve's `debruijinize`, `debruijinizeApp` and `closeLams` fold a term
into a Reader (`runReaderT . cata f`), their algebras `local`, `ask`,
`lift` and `sequence` at a Cofree's layer.

- **ReaderT**: `ReaderT r Identity a` (and transformers' `Reader r a`) is
  its newtype's `R -> A`, `ReaderT r (Either e) a` is `R -> Either E A`;
  the prelude's `hs.rd.*` and `hs.rde.*`: `>>=`, `>>`, `pure`, `fmap`,
  `<*>` (as `>>=`), mtl's `ask`, `local` (transformers' too), `asks`,
  `reader`, and `throwError` over Either; `lift` at `ReaderT r` the inner
  term under an environment it ignores; `runReaderT`/`runReader` the term.
- **CofreeF's instances** (free's Functor and Traversable at `CofreeF f
  a`) are Base's model's `cofreeFFmap`, `cofreeFTraverse` and
  `cofreeFSequence` (free's `traverse id`), as pairs' are (rule 19).
- **Derived Functor, Foldable and Traversable**: GHC's generated `fmap`,
  `<$`, `foldr`, `foldMap`, `null` and `traverse` are copied like a
  hand-written instance's (only derived Show was before); a pattern's
  type arguments are normal too (type families applied: Resolve's `LamT`
  and `LamVar`), and `pure`/`return` at a list is `[x]`.
- **Twins**: a layer of a monad's actions is a layer of functions, and
  Bend's Data holds none. Each of the package's types with type variables
  whose fields allow it has a twin `D.fn` (its last variable a Type, itself
  a Type, constructors `D.fn.C`, a field of another of the package's types
  at that variable the other's twin); the fold writes it wherever a type's
  last argument is a function or a twin, in types, patterns and terms,
  with `HsPrelude.CofreeF.fn` and `G.cata.fn`/`G.cata.cofree.fn` (the same
  nested matches, building the twin's layer). Twins are generated (not in
  the ledger). An `if` whose branches both use such a function takes it as
  an argument of each branch, applied once (Bend does not copy a Type).
- **Tests** (`tests/hs/Reader.hs`): Reader at Identity and over Either,
  cata into a Reader at a hand-written and at a derived Traversable,
  `sequence` at CofreeF, closeLams' `if` over one child: ex1..ex7 ok-law
  (5, 5, 8, 8, 5, 8, 8 laws, GHC's answers). Pair's `sequence` at a
  derived Traversable is now ok-law (2 out -> ok-law); the other tests: no
  def lost.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 19 (spec31, law40) | 446 | 98 | 285 | 113 |
| after rule 20 (spec34, law46, 834 s) | 445 | 98 | 286 | 113 |

No def lost its verdict; copies 797 -> 881 ok-check. `closeLams` checks;
`debruijinize` and `debruijinizeApp` (at Either ResolverError) now wait
only on the partial-function rule (`error` on an unexpected ParserTermL).
compileModules' frontier: 215 defs, 213 no; `error` 24, Map's `!` 18,
`show` at Fix 6, WriterT 5 (Resolve's letsToApps), LamBase 4.

## Telomare's rules, 21: WriterT, mconcat, Bifunctor's plain functions (2026-11-21)

Resolve's `letsToApps` builds its term in a `WriterT (Set String)
(Either ResolverError)` (the names a term refers to as the log), through
`cata` and `sequence` at a Cofree's layer.

- **WriterT** (`Control.Monad.Trans.Writer`, lazy or strict): `WriterT w
  Identity a` is `A & W`, `WriterT w (Either e) a` is `Either E (A & W)`;
  the prelude's `hs.wr.*` and `hs.wre.*` (Fold's `fd.pre.wr`,
  `fd.pre.wre`): `>>=`, `>>`, `pure`, `fmap`, `<*>` (as `>>=`), `liftA2`
  and `throwError`, each taking w's `mempty` and `<>` (Fold's `fd.wmon`, at
  w's type: lists, Sets, Maps). `writer` is the inner monad's `pure` of the
  pair, `lift` at `WriterT w` the inner `fmap` pairing with `mempty`;
  `WriterT`, `runWriterT` and `runWriter` are the term (a pattern
  `WriterT p` is `p`).
- **`mconcat`** at lists (`concat`) and Sets (HsSet's `unions`).
- **Data.Bifunctor's `first`, `second`, `bimap`** at Either and pairs take
  their functions plain (each calls it once), so a lambda over locals is
  in (they were templates, closed only).
- **Tests** (`tests/hs/Writer.hs`, letsToApps' shapes: a cata into
  `WriterT (Set String) (Either String)`, `lift . Left`, `Set.delete`,
  `null`, `sequence` at a derived Traversable inside Cofree): ex1..ex6
  ok-law (5, 2, 8, 8, 8, 8 laws, GHC's answers), the rest ok-check; the 17
  earlier test sets: no def moved.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 20 (spec34, law46) | 445 | 98 | 286 | 113 |
| after rule 21 (spec34, law48, 842 s) | 445 | 98 | 286 | 113 |

No def lost its verdict; copies 879 -> 882 ok-check (Resolve's
`ctraverse` at WriterT for BasicExprF, HighTermF, LamTermF). compileModules'
frontier: 211 defs, 209 no; `error` 24, Map's `!` 18, `show` at Fix 6,
LamBase 4. `letsToApps` waits on its `error` (an unexpected constructor),
LamBase's pattern synonyms and Cofree's `unwrap`/`embed`.

## Telomare's rules, 22: Show at Fix, more of Data.Map and Data.Set (2026-11-21)

- **Show at Fix f** (data-fix's instance, through f's Show1: IR.Base's
  `convertAbortMessage`, Core's `show` at RunTimeError): Base's model's
  `fixShowsPrec`, `fixShow`, `fixShows`, `fixShowList` (Spec's
  `sp.pc.ftab`, the type normal first, so a synonym like BasicExpr is one
  too), copied at f. A node's text at precedence d is its text
  unparenthesised under `showParen (d >= 11)`, so the model is a `cata` to
  that text, a child handed to `liftShowsPrec` as `fixShowsAt q` of its
  text: data-fix's answer when f's Show1 only prepends text (one built
  with base's Show combinators does; the laws hold it to GHC's). Checked in
  GHC against data-fix's instance at 4 precedences and two rests.
- **Data.Map and Data.Set** (`prelude/HsMapMore.bend`): `intersectionWith`,
  `restrictKeys`, `withoutKeys`, `fromSet`, `unionWithKey` (with
  `insertWithKey`), `unionsWith` (of a list; IntMap's has its key second
  in Data.Map's order, Spec's `sp.p5.second`), `split`, and Set's
  `intersection`; checked by 9 closed laws in Bend (one or two each).
- **Tests**: `tests/hs/ShowFix.hs` (telomare's Show1 shapes, one that
  reads the precedence, `show` at a class's type variable copied at Fix):
  ex1..ex5, ex7 ok-law (8, 8, 8, 5, 8, 8 laws), ex6 out (Show at a list of
  Fix, `fold:show-at-type`); `tests/hs/Maps.hs` (telomare's uses): ex1..ex10
  ok-law (8 laws each). The 17 earlier sets, Writer and Reader: no def
  moved.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 21 (spec34, law48) | 445 | 98 | 286 | 113 |
| after rule 22 (spec36, law49, 1037 s) | 445 | 98 | 286 | 113 |

No def lost its verdict; copies 882 -> 941 ok-check (24 out -> ok-check:
`convertAbortMessage` at Fix BasicExprF in 7 modules, PrettyPrint's
`showP1`/`showP`/`prettyPrint` at Term3F's Cofree and AbortableF), 35 new
copies. compileModules' frontier: 176 defs, 174 no (from 211/209); the
container functions are off it, `show` at Fix too (one left, inside
Size's `error` message, a local generalised over its type: Spec's
`sp.pl` runs after `sp.pc`). What is left is led by the partial
functions: `error` 24, Map's `!` 18, `minimum`/`minimumBy` 2, `!!` 1;
across telomare 61 of the 488 out functions wait only on them.

## Telomare's rules, 23: fold, until, copies' names (2026-11-21)

- **Data.Foldable's `fold`** at any container (Resolve's freeVarsDeep,
  pruneBindings, validateVariables; Surface's patternBinders; Size's
  buildUnsizedLocMap): Base's model's `foldMonoid`, `foldr (<>) mempty`
  (the same value at a lawful Monoid), at the container and the Monoid
  (Spec's `sp.pc.mtab`); free's `foldr` at CofreeF is the model's
  `cofreeFFoldr`, as its fmap and traverse are.
- **`until`** (pruneBindings' fixpoint): Base's model's, base's
  definition, copied at its known p and f and written with fuel.
- **Copies' names**: a copy at known arguments is `NAME__..._fHASH`, the
  hash now of the arguments with their types normal, so a recursive call
  inside the copy, whose lambda's types the copy has normal (`List Char`
  where the original said `String`), is the copy's own (until's was
  not). Copies whose arguments name a synonym are renamed;
  `help/LedgerN.hs` compares ledgers without the hash.
- **Tests**: `tests/hs/FoldM.hs` (patternBinders', freeVarsDeep's,
  buildUnsizedLocMap's and validateVariables' shapes): ex1..ex5 ok-law (8
  laws each). `tests/hs/Until.hs`: ex2 ok-law (until at Int, fuel), the
  copy at pruneBindings' shape ok-check, ex1 out: `reach` is
  `fold:closure-argument`, its `until`'s arguments name a local function
  (`expand`, a where function over a local Map), which the copy takes as a
  parameter and Bend takes only closed. The 17 earlier sets, ShowFix,
  Maps, Writer, Reader: no def moved.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 22 (spec36, law49) | 445 | 98 | 286 | 113 |
| after rule 23 (spec38, law49, 1073 s) | 445 | 98 | 286 | 113 |

No def lost its verdict; copies 941 -> 960 ok-check, 19 new (the model's
copies at telomare's containers). The defs `fold` blocked now wait on
others: freeVarsDeep on `foldMap` with a lambda over a local function
(patternRefs), pruneBindings on until's arguments naming a local function
(the same: a closure over a local function, next), buildUnsizedLocMap on
AbortableF's derived `foldr`, base's default (GHC derives it at a type
whose variable is phantom), patternBinders on its type variable. Still
first on the path: the partial functions (`error` 24, Map's `!` 18).

## Telomare's rules, 24: local functions in known arguments, ifs out of arguments, foldMap, filter, the default foldr (2026-11-21)

- **A local function in a known argument** (a nonrecursive let's or
  where's, Spec's `sp.fa.lfuns`) is its value there: its lambda (an
  applied one reduced, `sp.beta`), or, with no parameters but a function
  (`patternRefs = cata palg where ..`), its right-hand side under a let of
  its where-bindings. So a copy's parameters are its free locals, not a
  closure over them: pruneBindings' `until (\s -> expand s == s) expand
  seed` is a copy of until at bmap, a Map. An argument has the local
  functions that name a local or the def they are in; one that names the
  def (a recursion through the copy) has all of them, so the copy takes no
  template and the recursion is a group the fold writes with fuel. A
  closed local function that names neither stays a template, as it was.
- **A def with a class at a known argument**: a call of its dictionary
  copy (asked for by p4 in the same top) is the def's call at the copy's
  types (`sp.fa.dq.find`), when the argument names a local or, inside a
  lambda, the def the call is in; else the dictionary copy takes it as a
  closed template, as before (pair's `traverse (\x -> if ..)` stays so).
- **Ifs and lets out of arguments** (`sp.ifl`, after `sp.beta`): `f (if c
  then a else b)` is `if c then f a else f b`, `f (let ds in e)` is `let
  ds in f e`, so the if is where the fold knows its type (EAL's
  `mergeClasses`: `pure $ if la >= lb then a else b`). Not over `&&` and
  `||`, not out of a lambda, a case or a tuple.
- **Base's model**: `foldMap` at a list is `foldMapMonoid` (Foldable's
  default, `foldr (\x acc -> f x <> acc) mempty`; at a package's derived
  Foldable it stays the instance's), GHC.List's `filter` is the model's
  `filter`, and base's default `foldr`, `$dmfoldr` (GHC's derived Foldable
  leaves it at a type whose variable is phantom: AbortableF,
  IndexedInputF), is `foldrDefault`, `foldr` over `foldMap (\x -> [x])`.
  A generated method with no parameters that is a function and not a
  lambda (`$cfoldr = $dmfoldr`) takes its arguments (`sp.p0.eta`), so a
  template reaches the def through it.
- **Tests**: `tests/hs/Prune.hs` (pruneBindings' and freeVarsDeep's
  shapes with a local function, filter at a section over a local): prune,
  reach, ex1..ex4 ok-law, free ok-check (a Set). `tests/hs/IfArg.hs`:
  pick, dist, grow, nested, halves, ex1, ex2, ex4 ok-law; `both` (an if in
  a tuple) and `lazyAnd` (under `&&`) out, fold:if-in-argument, as
  designed. `tests/hs/Phantom.hs`: sumAb, ab, ex1..ex3 ok-law (were out,
  survey: `$dmfoldr`). `tests/hs/FreeDeep.hs` (freeVarsDeep's shape
  whole): out, see below. The 23 earlier sets (the 17, ShowFix, Writer,
  Reader, Maps, FoldM, Until) against their last ledgers: rv 2 out ->
  ok-law, Until's reach and ex1 out -> ok-law, nothing lost (each set
  has the model's new generic defs, out on their own as the others are).

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 23 (spec38, law49, 1073 s) | 445 | 98 | 286 | 113 |
| after rule 24 (spec49, law49, 1303 s) | 443 | 98 | 288 | 113 |

Own: mergeClasses and Levels' globalEnv out -> ok-check, no own def
lost. Copies (`help/LedgerN.hs`, without the hash): 935 -> 969 ok-check;
10 out -> ok-check, 6 ok-check -> out: four now hold the local function
they took as a template, and its Map `!` (EAL's foldl copies at
eliminate's and simplexSolve's), one a guard that falls through, one a
let in a tuple (validateVariables'); every def calling those six was out
before and is now. Frontier from compileModules: 188 reached, 186 not
ok, first `error` 25, Map's `!` 22; 69 of telomare's not-ok defs wait
on partial functions only. Spec takes 366 s on telomare (was 175 s).

Still out: freeVarsDeep and pruneBindings (which calls it). The group the
fold now makes (freeVarsDeep, its alg and patternRefs' palg, the foldMap
and foldr copies) has freeVarsDeep = `cata alg`, a member with no
parameters whose cata takes the group's algebra as a template naming the
fuel, which Bend refuses (law: "expected a term, observed '~'"). Next: a
group member that is a cata at the group's algebra is a member of its
own, the cata's recursion written with the fuel.

## Telomare's rules, 25: local catas, a group's point-free members (2026-11-21)

- **Local catas** (`fd.lc.*`, Fold.bend): a cata whose algebra calls back
  the def it is in, or at a functor with a list of its recursive variable
  (EF's `[(Fix PF, r)]`, UnprocessedParsedTermF's LetUPF, ListUPF and
  CaseNodeUPF, which have no `G.cata`: the role `FrList`), is a def of
  its own at the call, `D.cH` (H a hash of the call's functor, types and
  algebra; ledger ok-gen): matches at Fix or Cofree and the functor's
  constructors, the algebra applied to the layer, recursive fields calls
  of `D.cH`, a list, Maybe, pair or other functor of them a call of a
  def `D.cH.hP` mapping it. They join D's group, so the algebra is
  applied, not handed over as a template naming the fuel ("expected a
  term, observed '~'" before).
- **A group's point-free members** (`fd.mu.ab*`, `fd.mu.sat`): a member
  whose answer is a function (`freeVarsDeep = cata alg`, `patternRefs =
  cata palg`) takes its arguments as parameters in the group (g.Out's
  fields are data: "expected Data, observed Type" before), its calls in
  the group given the arguments they are applied to (else eta-expanded),
  the lambda again outside the group.
- Fold's module items are written once, `fd.mod.its`, for Fold.bend's
  fd.module and Law.bend's lw.module (Law's had its own copy, which the
  first build missed). Bend checks a def's calls only against defs above
  it ("an unfilled law is a dead claim" for one below).
- **Tests**: `tests/hs/FreeDeep.hs`: ex1, ex2 ok-law (were out), freeD
  ok-check. The 27 other sets against their last ledgers: no moves,
  nothing lost.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 24 (spec49, law49, 1303 s) | 443 | 98 | 288 | 113 |
| after rule 25 (spec49, law50, 1351 s) | 440 | 99 | 290 | 113 |

Own: Resolve's pruneBindings out -> ok-law, freeVarsDeep and Fast's
findAbort out -> ok-check; nothing lost. Copies: 969 -> 1006 ok-check,
360 -> 323 out (39 out -> ok-check, 1 -> ok-law), nothing lost. Out
reasons left (own and copies): survey 510 (partial functions first:
`error`, Map's `!`), dep 117, fold 109 (recursive-local 21, show-at-type
20, closure-argument 11, monad-at-type 10, local-patbind 9).

## Telomare's rules, 26: a local named as a def, lets and ifs out of tuples, C {}, maybe at a function (2026-11-21)

- **A local named as one of the module's defs** its top refers to is
  renamed NAME_ID (`sp.lr`, Spec.bend): GHC's record update binds the
  new value to a local named as the field, then calls the selector
  (freshInt: "expected a function type, observed HsInt" before).
- **Lets and ifs out of a tuple's element** (`sp.ifl.tup`, depth 8): a
  record update in a pair (Fast's tickApply, tickGate).
- **`C {}` at a constructor without field names**: a wildcard per field
  (`fd.pfields.n`; IC's valueKind: "a ICKind.ICRef pattern with 2 fields").
- **`hs.maybe`/`hs.either` take a Type answer** (a monad's action):
  EAL's walkTau ("expected Data, observed Type").
- **Tests**: `tests/hs/RecUp.hs` (help/ru): bump, tick, isRef, adder,
  ex1..ex4 ok-law (were out: let-in-argument, the pattern, Data vs Type).
  The other 28 sets: rv 1 out -> ok-check, 1 -> ok-law; IfArg's `both`
  and ex3 out -> ok-law (an if in a tuple); nothing lost.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 25 (spec49, law50, 1351 s) | 440 | 99 | 290 | 113 |
| after rule 26 (spec50, law51, 1335 s) | 423 | 100 | 306 | 113 |

Own out -> ok-check: EAL's freshInt, freshB, freshTau, freshCode,
freshSigma, bottomSigma, builtinCode, exposedClasses, occurs,
packageClass, shapeOfSigma, walkTau; Fast's tickApply, tickGate; IC's
dupPlanFor, materialValue; valueKind out -> ok-law. Copies 1006 -> 1008
ok-check. Nothing lost.

## Partial functions: the user's answer (2026-11-21), the plan

"As a failure value, as the bend branch does (Crash/SErr): the function
returns Either String a, callers pass it on, and the tests check GHC's
error message too." The plan, first order first:

1. The survey takes `error`, `errorWithoutStackTrace`, `undefined`,
   Data.Map's `!`, `!!`, `head`, `tail`, `last`, `init`, `fromJust` as
   cata's (info `partial:NAME`, not out).
2. The fold writes each as an Either: `hs.fail(A, msg)` is `Inl{msg}`,
   `HsMap.at` is Map's `!` ("Map.!: given key is not an element in the
   map"), the list ones with GHC's messages.
3. A pass over the module's items (after local catas, before groups): a
   def that calls one of them, or a def that does, answers
   `Either<String, R>`; in each answer (a body's or a case's) its partial
   calls are bound innermost first with `hs.either.bind` (the callee's
   answer type from its signature, its type arguments put in), an `if`
   with a partial branch is an Either itself, a let's value is bound
   before its body. A partial call under a user's lambda is out
   (`fold:partial-in-lambda`) for now: a monad's continuation is one,
   so monadic code comes after, as the error layer under the monad.
   Groups and local catas need nothing more: their members are defs.
   Later modules learn which defs are partial with the types.
4. Law: a partial def's GHCi line runs it under `lawRunE`, GHC's
   `ErrorCall` message becoming `Inl{msg}` and an answer `Inr{v}`, so
   the laws check the message.

## Telomare's rules, 27: partial functions as failure values (2026-11-21)

The plan above, its first part (plain code), built:

- **The survey** takes `error`, `errorWithoutStackTrace`, `undefined`,
  `head`, `tail`, `last`, `init`, `!!`, `fromJust` and Map's `!` (info
  `partial:NAME`, not out); the other partial ones (`foldr1`,
  `maximum` at a list, `minimumBy`, ...) stay out.
- **prelude/HsPartial.bend**: each as an Either, GHC's messages
  (`HsList.error`, `HsList.head`, ..., `HsList.index`, `HsMap.at`), the
  fold's tables (fd.bftab2.pt, fd.dm.specs.map6) writing them.
- **The partial pass** (Fold.bend's `fd.pt`, after the local catas,
  before the groups; README's "Partial functions"): the partial defs to a
  fixed point, their answers Eithers, the calls bound innermost first; a
  lambda applied at once (a comprehension's copy) whose body is a partial
  call is that call; a partial call under any other lambda is out,
  `fold:partial-in-lambda`. A later module learns an earlier one's
  partial defs from the package's exports (fd.dt.export: the signature).
- **Out before the first check**: a def a pass after the fold left a
  `BtTodo` in goes out with its reason (fd.predrop; before, its ?TODO
  failed the whole module's check, 239 defs "check:raw" in the first run).
- **Print** (agda2bend's ToBend/Print.bend, 644ea88): a let inside a
  term is a parenthesized body, `(x = v; b)` (it was ?TODO).
- **Law**: a partial def's GHCi call is under `LawEw`, whose `lawSx`
  answers GHC's `ErrorCall m` as `Inl m`, an answer as `Inr`.
- **Tests**: `tests/hs/Partial.hs` (help/pt): width, half, ex1..ex9,
  offAt, firstOr ok-law (GHC's messages checked: 26 Inl answers), look
  ok-check (no law at a Map argument), ex10 (`map half`) out
  fold:partial-in-lambda. The 28 other sets: nothing lost; Base's model's
  iterateIndex out -> ok-check in each, Iter.hs 8 out -> ok-law, 4 ->
  ok-check.

| telomare's own defs (not the model's) | out | ok-law | ok-check | types |
|---|---|---|---|---|
| after rule 26 (spec50, law51, 1335 s) | 423 | 100 | 306 | 113 |
| after rule 27 (spec50, law54, 1542 s) | 420 | 102 | 307 | 113 |

Own out -> ok-law: Levels' offAt, Indent's indentSansFirstLine; out ->
ok-check: Expand's accessAt. Copies 1008 -> 1026 ok-check (EAL's
simplex comprehensions with Map's `!`, the iterateIndex copies,
foldGateResult, unsizedTestSuper, sizedRecursionChain, varB). Nothing
lost. 53 defs the survey left out for a partial function now reach the
fold and are out for other rules: local-patbind 8, closure-argument 6,
guard-falls-through 5, partial-in-lambda 4, if-in-argument 4, law's
"expected Data, observed Type" 4. Survey: compileModules' frontier 188
reached / 186 no -> 127 / 125 (partial:error and base:! gone from it).

Next for the partial functions: a partial call under a lambda, a cata's
algebra first (term3ToUnsizedExpr, convertPT, getInputLimits: an Either
cata, each layer's children bound before the algebra), then monadic code
(the error under the monad).
