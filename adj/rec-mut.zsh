#!/usr/bin/env zsh
# adj/rec-mut.zsh: mutants of section 14 (definitions that call each other,
# functions as values), each a sed on a copy of adj/Core.bend; PROOF.bend
# must fail with each, and REC.bend with each that changes Haskell's meaning
# (eval.hr and what it uses).  Prints one line a mutant.  BEND the bend
# (default: cata's run/gcroot-bend).
set -u
src=${0:A:h}
B=${BEND:-$(readlink -f $src/../run/gcroot-bend)/bin/bend}
export BEND_NO_TELEMETRY=1
tmp=$(mktemp -d /tmp/ct-mut.XXXXXX)
typeset -A M
M[F-comp-swapped]='s/      BrComp{F.hr(g), F.hr(f)}/      BrComp{F.hr(f), F.hr(g)}/'
M[F-call-next]='/^def F.hr(/,/^def F.hd(/ s/      BrCall{i}$/      BrCall{1n+i}/'
M[F-app-fails]='/^def F.hr(/,/^def F.hd(/ s/      BrApp{}$/      BrTm{BFail{}}/'
M[F-default-dropped]='s/      BdCons{F.hr(t), enc(d), F.hd(es)}/      BdCons{F.hr(t), BvUnit{}, F.hd(es)}/'
M[G-default-dropped]='s/      HdCons{G.br(t), dec(d), G.bd(es)}/      HdCons{G.br(t), HvUnit{}, G.bd(es)}/'
M[G-link-swapped]='/^def bd.app(/,/^def bclo(/ s/      BdCons{t, d, bd.app(fs, es)}/      bd.app(fs, BdCons{t, d, es})/'
M[b-app-swapped]='/^def m.app(/,/^def eval.br(/ s/      k(i, BvPair{e, a})/      k(i, BvPair{a, e})/'
M[b-case-swapped]='s/      m.case(y, a => eval.br(k, ds, f, a), b => eval.br(k, ds, g, b))/      m.case(y, a => eval.br(k, ds, g, a), b => eval.br(k, ds, f, b))/'
M[b-fuel-out-fails]='/^def eval.br(/,/^def g.case(/ s/      Some{bd.dv(ds, i)}$/      None{}/'
M[g-fuel-out-fails]='/^def eval.gr(/,/^def F.hr(/ s/      Some{hd.dv(ds, i)}$/      None{}/'
M[until-swapped]='s/HrIf{HrTm{p}, HrTm{HId{}}, HrComp{HrCall{0n}, HrTm{s}}}/HrIf{HrTm{p}, HrComp{HrCall{0n}, HrTm{s}}, HrTm{HId{}}}/'
M[malg-swapped]='s/HComp{HCase{HComp{s1, HPr{HSnd{}, HFst{}}}, HComp{s2, HPr/HComp{HCase{HComp{s2, HPr{HSnd{}, HFst{}}}, HComp{s1, HPr/'
M[h-app-swapped]='/^def r.app(/,/^def eval.hr(/ s/      k(i, HvPair{e, a})/      k(i, HvPair{a, e})/'
M[h-clo-swapped]='s/^  HPr{HLit{i}, HId{}}$/  HPr{HId{}, HLit{i}}/'
M[h-if-swapped]='s/      r.if(eval.hr(k, ds, c, x), eval.hr(k, ds, a, x), eval.hr(k, ds, e, x))/      r.if(eval.hr(k, ds, c, x), eval.hr(k, ds, e, x), eval.hr(k, ds, a, x))/'
M[h-call-first]='/^def hd.at(/,/^def hd.dv(/ s/      hd.at(es, j)/      t/'
M[h-error-is-out]='/^def r.bind(/,/^def r.pair(/ s/          RDone{None{}}/          ROut{}/'
M[h-pair-drops]='/^def r.pair(/,/^def r.cons(/ s/              RDone{h.pair(Some{u}, w)}/              RDone{w}/'
for k in ${(ko)M}; do
  w=$tmp/$k; mkdir -p $w; cp $src/Core.bend $src/PROPOSED.bend $src/PROOF.bend $src/REC.bend $w/
  sed -i "${M[$k]}" $w/Core.bend
  if cmp -s $src/Core.bend $w/Core.bend; then print "$k: NOT APPLIED"; continue; fi
  r=$($B $w/PROOF.bend --check-only 2>&1 | head -1); c=$($B $w/REC.bend --check-only 2>&1 | head -1)
  loc=$($B $w/PROOF.bend --check-only 2>&1 | grep -m1 '^Location' )
  print "$k: PROOF $r ($loc); REC $c"
done
rm -rf $tmp
