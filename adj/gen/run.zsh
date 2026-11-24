#!/usr/bin/env zsh
# adj/gen/run.zsh OUT [MODULES]: the model's fragment tried against GHC and
# against cata itself.  Gen.bend writes MODULES (8) modules of 25 random
# typed programs each (Core.bend's Ex, its defs' types over Natural, Bool,
# (), pairs, Either and lists), as Haskell; then
#   1. GHC runs each at 8 inputs: its answer is the model's (ev.def, which
#      is eval.h (cc.def t) and F's Bend through enc: PROPOSED.bend's
#      cc.def.ok and cc.F) wherever the model answers; where the (strict)
#      model errs GHC errs, or answers by laziness (counted apart)
#   2. with SPEC and LAW (bend/Spec.bend's and bend/Law.bend's binaries),
#      cata's own F takes them, as one package: how many of the programs it
#      takes (the model's F takes every one), and why not the rest; each
#      law is GHC's answer at an input, checked by Bend
#   BEND the bend, GHC a directory holding ghc and runghc, HSX hs-export.
# Prints PASS when no answer differs.  OUT is made anew.
set -u
here=${0:A:h}
out=${1:A} mods=${2:-8}
bend=${BEND:-bend}
[[ -n ${GHC:-} ]] && export PATH=$GHC:$PATH
[[ -e $out ]] && { print "$out exists"; exit 1 }
mkdir -p $out/src $out/chk
BEND_NO_TELEMETRY=1 $bend $here/Gen.bend -o $out/gen > $out/gen.log 2>&1 || { tail -5 $out/gen.log; exit 1 }
S=0 E=0 L=0 D=0
for ((k = 0; k < mods; k++)); do
  $out/gen hs Frag$k $((k * 25)) 25 > $out/src/Frag$k.hs
  $out/gen chk Frag$k $((k * 25)) 25 > $out/chk/Chk$k.hs
  runghc --ghc-arg=-w --ghc-arg=-i$out/src:$here $out/chk/Chk$k.hs > $out/chk/Chk$k.out 2>&1
  l=$(tail -1 $out/chk/Chk$k.out)
  [[ $l =~ '^same ([0-9]+), both err ([0-9]+), GHC answers where the strict model errs ([0-9]+), differ ([0-9]+)$' ]] || { print "Chk$k failed:"; tail -5 $out/chk/Chk$k.out; exit 1 }
  S=$((S + match[1])) E=$((E + match[2])) L=$((L + match[3])) D=$((D + match[4]))
  grep '^DIFFER' $out/chk/Chk$k.out
done
print "GHC against the model: $((mods * 25)) programs, $((S + E + L + D)) answers: same $S, both err $E, GHC answers where the strict model errs $L, differ $D"
bad=$D
if [[ -n ${SPEC:-} && -n ${LAW:-} ]]; then
  pre=${here:h:h}/prelude
  mkdir -p $out/ex $out/o $out/l
  { print -- "-i$out/src"; print -- "-i$pre"; print -- "-XHaskell2010"; print -- "--"; print -- "$pre/Cata/Base.hs"; print -l $out/src/*.hs } > $out/args
  ${HSX:-hs-export} --package $out/ex $out/args > $out/ex.log 2>&1 || { tail -5 $out/ex.log; exit 1 }
  $SPEC $out/o $(cat $out/ex/modules.txt) > $out/o.log 2>&1 || { tail -5 $out/o.log; exit 1 }
  (cd $out && BEND=$bend GHC="$(whence -p ghc) -i$out/src -i$pre -XHaskell2010 -fobject-code -outputdir $out/obj" nice -n 10 ${LAW:A} --package l $(sed "s#^$out/##" o/modules.txt) > l.log 2>&1) || { tail -5 $out/l.log; exit 1 }
  awk -F'\t' '$1 ~ /Frag[0-9]+\.sexp$/ && $2 ~ /^d[0-9]+$/ {n++; c[$3]++; if ($3 == "ok-law") {split($4, a, ":"); w += a[2]} if ($3 == "out") {r = $4; sub(/^(law|check):.*/, "&", r); sub(/:.*/, "", r); if (r == "fold") r = $4; o[r]++}}
    END {printf "cata itself: %d programs, taken %d (ok-law %d with %d laws, ok-check %d, ok-type %d), out %d\n", n, n - c["out"], c["ok-law"], w, c["ok-check"], c["ok-type"], c["out"]; for (k in o) printf "  out %d %s\n", o[k], k}' $out/l/ledger.tsv | sort -k1,1 -k3,3rn
fi
if (( bad == 0 )); then print PASS; else print FAIL; exit 1; fi
