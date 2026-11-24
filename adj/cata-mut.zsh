#!/usr/bin/env zsh
# adj/cata-mut.zsh: mutants of section 13 (catamorphisms), each a sed on a
# copy of adj/Core.bend; PROOF.bend must fail with each, and CATA.bend with
# each that changes Haskell's meaning (eval.h, eval.lz).  Prints one line a
# mutant.  BEND the bend (default: cata's run/gcroot-bend).
set -u
src=${0:A:h}
B=${BEND:-$(readlink -f $src/../run/gcroot-bend)/bin/bend}
export BEND_NO_TELEMETRY=1
tmp=$(mktemp -d /tmp/ct-mut.XXXXXX)
typeset -A M
M[kids-swapped]='s/          b.cons(eval.b(t, k), eval.b(t, ks))/          b.cons(eval.b(t, ks), eval.b(t, k))/'
M[shape-dropped]='s/          Maybe.bind(\&2, BV, BV, eval.b(t, ks), rs => eval.b(s, BvPair{sh, rs}))/          Maybe.bind(\&2, BV, BV, eval.b(t, ks), rs => eval.b(s, BvPair{BvUnit{}, rs}))/'
M[F-drops-alg]='s/      BCata{F(s)}$/      BCata{BId{}}/'
M[G-drops-alg]='s/      HCata{G(s)}$/      HCata{HId{}}/'
M[nil-fails]='/^    case BCata{s}:/,/^        case _:/ s/          Some{BvNil{}}/          None{}/'
M[alg-before-kids]='s/          Maybe.bind(\&2, BV, BV, eval.b(t, ks), rs => eval.b(s, BvPair{sh, rs}))/          Maybe.bind(\&2, BV, BV, eval.b(s, BvPair{sh, BvNil{}}), rs => eval.b(t, ks))/'
M[lalg-head-last]='s/HComp{HFold{HUnit{}, HFst{}}, HFst{}}/HComp{HFold{HUnit{}, HSnd{}}, HFst{}}/'
M[lazy-forces-kids]='s/          Some{LvCons{eval.lz(t, k), eval.lz(t, ks)}}/          Maybe.bind(\&2, LV, LV, eval.lz(t, k), u => Some{LvCons{Some{u}, eval.lz(t, ks)}})/'
M[lazy-kids-swapped]='s/          Some{LvCons{eval.lz(t, k), eval.lz(t, ks)}}/          Some{LvCons{eval.lz(t, ks), eval.lz(t, k)}}/'
M[h-kids-swapped]='s/          h.cons(eval.h(t, k), eval.h(t, ks))/          h.cons(eval.h(t, ks), eval.h(t, k))/'
M[h-shape-dropped]='s/          Maybe.bind(\&2, HV, HV, eval.h(t, ks), rs => eval.h(s, HvPair{sh, rs}))/          Maybe.bind(\&2, HV, HV, eval.h(t, ks), rs => eval.h(s, HvPair{HvUnit{}, rs}))/'
for k in ${(ko)M}; do
  w=$tmp/$k; mkdir -p $w; cp $src/Core.bend $src/PROPOSED.bend $src/PROOF.bend $src/CATA.bend $w/
  sed -i "${M[$k]}" $w/Core.bend
  if cmp -s $src/Core.bend $w/Core.bend; then print "$k: NOT APPLIED"; continue; fi
  r=$($B $w/PROOF.bend --check-only 2>&1 | head -1); c=$($B $w/CATA.bend --check-only 2>&1 | head -1)
  loc=$($B $w/PROOF.bend --check-only 2>&1 | grep -m1 '^Location' )
  print "$k: PROOF $r ($loc); CATA $c"
done
rm -rf $tmp
