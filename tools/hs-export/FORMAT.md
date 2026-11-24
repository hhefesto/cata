# hs-export's output format (version 1, GHC 9.10.3)

hs-export type-checks one Haskell module with GHC 9.10.3's API and writes
GHC's typechecked syntax as S-expressions, for cata (a Bend program) to
translate. It makes no translation decisions: it keeps every binding, type,
class and instance, drops only source parentheses, ticks and coercions, and
names whatever it does not export as `(unsupported "Constructor")`, so the
Bend side can ledger it. This file is the contract between the two programs.

    hs-export OUT.sexp FILE.hs
    hs-export --package OUTDIR ARGS

The first form type-checks one module, which may import only GHC's own
packages (`base` and the other boot packages). The second type-checks a
package's modules together: ARGS is a file of GHC flags, one per line (a
package's `-i`, `-X` and `-package-db`), a line `--`, then the modules'
files, one per line. GHC loads them all (no code), then each is exported
as the first form exports one, to `OUTDIR/M_N.sexp` for module `M.N` (a
Bend module path is plain names), and `OUTDIR/modules.txt` lists those
files in dependency order, each after every module of the package it
imports. A module GHC rejects, or one that imports a rejected one, is
written as its header and one `(error "GHC's message")`.

## Lexical syntax

The same as agda2bend's agda-export, so ToBend/Sexp.bend reads both:

    sexp   ::= atom | int | string | "(" sexp* ")"
    atom   ::= [A-Za-z0-9_.-]+
    int    ::= [0-9]+ | "(neg " [0-9]+ ")"
    string ::= '"' ( [^"\\] | '\"' | '\\' )* '"'

Strings are UTF-8 with `\"` and `\\` as their only escapes; a raw newline
may sit inside one. Every name is a string. Each top-level expression is
followed by a newline.

## The file

    (hs-export 1 (ghc "9.10.3") (file PATH))
    (module NAME ((import MOD open|qualified) ...))
    TYCON ...          one per type, newtype, synonym and class it defines
    (instance CLSMOD CLS (TYPE ...) DFUN SPAN (cls (TV...) (METHOD...) NSUPER)) ...
    (faminst FAMMOD FAM (ARG ...) RHS) ...  one per type family instance
    (top BIND) ...     its bindings, in source order

## Names

    (g MOD NAME KIND)  a top-level or imported name; KIND is var, con, sel
                       (a record selector), dfun (an instance's dictionary)
                       or (method CLSMOD CLS)
    (l NAME N)         a local; N numbers the locals of the file in order of
                       first sight
    (self X)           a recursive reference, inside its own binding group, to
                       the binding X (GHC's monomorphic Id of X)
    (bv VAR TYPE)      a binder and the type GHC gave it

## Types

    (tv NAME) (tapp T T) (tc MOD NAME ARG...) (tfun A B)
    (tctx CONSTRAINT T)  (tforall NAME T) (tnum N) (tstr S) (tchar S) tcoercion

`tc` drops invisible (kind) arguments. Lists are `(tc "GHC.Types" "List" T)`,
tuples `(tc "GHC.Tuple" "Tuple2" A B)`, unit `(tc "GHC.Tuple" "Unit")`.

## Types, classes, instances

    (data NAME (TV...) ((con NAME (FIELD...) (ARGTYPE...) (ex NEX NTHETA))...) SPAN)
    (newtype ...)                         as data
    (synonym NAME (TV...) TYPE SPAN)
    (class NAME (TV...) ((method NAME TYPE)...) (SUPERCLASS...) SPAN)

A data type's `TV...` are its visible variables, the ones a `tc` of it
applies: a kind variable GHC adds (`data Resource a` with `a` unused, its
kind generalised to `k` under PolyKinds, GHC2021's default) is not one.
`ex` counts a constructor's existential variables and its own constraints.
An instance's `cls` is its class's variables and dictionary fields:
NSUPER superclasses, then the methods in this order.
A type family instance (`faminst`, an associated type's too) gives the
family, its arguments (their variables free) and its right-hand side.
SPAN is `(span L1 C1 L2 C2)` or `nospan`.

## Bindings

    (fun VAR TYPE SPAN MATCHES)           f p1 p2 | g = e where ...
    (patbind PAT SPAN GRHSS)              (a, b) = e
    (varbind VAR TYPE EXPR)               generated
    (abs (TV...) (EVBINDER...) ((export VAR TYPE)...) (EVBINDS...) (BIND...) SPAN)

A strict variable binding, `!x = e` (BangPatterns), is a FunBind in GHC
with the strictness in its match's context; it is written as the pattern
binding it means, `(patbind (pbang (pvar BINDER)) SPAN GRHSS)`, so a
consumer that reads `(fun ..)` as a lazy let does not lose the bang.

`abs` is GHC's AbsBinds: a generalised group. Its binds refer to each other
through `self`; its evidence binders are the dictionaries it takes, and its
evidence bindings the dictionaries it builds.

    (matches (ARGTYPE...) RESTYPE source|generated (MATCH...))
    (match (PAT...) GRHSS)
    (grhss (GRHS...) LOCALBINDS)
    (grhs (GUARD...) EXPR)                a guard is a statement
    (binds (rec BIND...)|(nonrec BIND...) ...)

`generated` marks code GHC wrote (derived instances).

## Statements

    (last E) (bind PAT E) (body E) (letstmt LOCALBINDS)

## Expressions

    VAR  (app F A)  (tyapp E TYPE)  (evapp E EVIDENCE)  (tylam TV E)
    (evlam EVBINDER E)  (evlet EVBINDS E)  (cast E)
    (olit VAL TYPE WITNESS)               an overloaded literal: VAL is
                                          (int N), (frac NUM DEN TEXT) or
                                          (string S); WITNESS is GHC's
                                          fromInteger/fromRational call
    (char CODE) (string S) (int N) (integer N TYPE) (rat FRAC TYPE)
    (lam single|case|cases MATCHES)
    (negapp E NEGATE)  (tuple E...)  (missing TYPE)
    (case E MATCHES)  (if C T E)  (multiif TYPE (GRHS...))
    (let LOCALBINDS E)  (do do|listcomp|... TYPE (STMT...))
    (list ELEMTYPE (E...))  (reccon CON ((field SEL E)...) nodots|dotdot)
    (arith WITNESS (from A)|(fromthen A B)|(fromto A B)|(fromthento A B C))
    (expanded ORIG E)                     E is GHC's expansion of an
                                          operator section, an operator
                                          application, a record update or a
                                          do block; ORIG is (expr CTOR),
                                          stmt or pat

Evidence is a Core expression: a dictionary variable, `(tyapp D TYPE)` or
`(evapp D D)`.

## Patterns

    (pwild TYPE) (pvar BV) (plazy P) (pas BV P) (pbang P)
    (plist TYPE (P...)) (ptuple (P...))
    (pcon CON (ARGTYPE...) (args P...)|(fields (pfield SEL P)...))
    (pview E P) (plit LIT) (pnlit OLIT pos|neg TYPE) (pnplusk BV OLIT)
