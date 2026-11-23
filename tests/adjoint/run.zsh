#!/usr/bin/env zsh
# tests/adjoint/run.zsh SQDIR LAWOUT MOD WORK DIR=PATH...: whether a
# hand-written Bend implements a Haskell module, by squares (PLAN.md, "cata
# as a functor", flavour 4).
#   SQDIR: PROPOSED.bend (the squares phi(F.h(x)) == W.b(phi(x)), the
#          human's) and PROOF.bend (their proofs); PROPOSED.bend imports
#          cata's Bend of h's module as F from ./l/MOD, and the hand-written
#          side from other directories, ./DIR/...
#   LAWOUT: a law run's OUT (MOD and the files it imports, with GHC's
#           example laws in MOD)
#   WORK: a new directory; LAWOUT is copied to WORK/l, each PATH to
#         WORK/DIR, nothing is written elsewhere
# 1. For every input: bend PROOF.bend --check-only, then --verdict (BendTT's
#    kernel), and the verdict again without the squares the kernel calls
#    out of its scope.
# 2. At GHC's answers (bend/Adj.bend): each example law of F.h gives each
#    square calling F.h an instance with GHC's answer in F.h(x)'s place,
#    checked (--check-only and --verdict); and the mutants, two squares of
#    one shape with their b's swapped, at GHC's answers and in PROOF.bend.
# BEND names the bend; LEAN a directory holding Lean 4.34.0's lean.  PASS
# when every proof checks, the verdict holds on the squares in the kernel's
# scope and every instance at GHC's answers checks; a mutant that survives
# is reported (two b's may agree everywhere), not a failure.
set -u
here=${0:A:h}
sq=${1:A} lawout=${2:A} mod=$3 work=${4:A}
shift 4
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
export BEND_NO_TELEMETRY=1
mkdir -p $work/l
cp $lawout/*.bend $work/l/
for a in "$@"; do
  d=${a%%=*} p=${a#*=}
  mkdir -p $work/$d; cp ${p:A}/*.bend $work/$d/
done
cp $sq/PROPOSED.bend $sq/PROOF.bend $work/
fail=0
print "== for every input (PROOF.bend)"
c=$(cd $work && $bend PROOF.bend --check-only 2>&1)
print "check:   ${c%%$'\n'*}"
[[ $c == "ALL PROOFS CHECK"* ]] || { print $c | head -20; fail=1 }
v=$(cd $work && $bend PROOF.bend --verdict 2>&1)
print "verdict: ${v//$'\n'/ | }"
print "squares: $(grep -c '^law ' $work/PROPOSED.bend)"
out=(${(f)"$(print -r -- $v | sed -n 's/^- PROPOSED\.\([A-Za-z0-9_.]*\): .*/\1/p')"})
if (( ${#out} )); then
  mkdir -p $work/k
  for d in $work/*(/); do [[ ${d:t} == (k|mut.*) ]] || ln -sfn ../${d:t} $work/k/${d:t}; done
  cp $work/PROPOSED.bend $work/PROOF.bend $work/k/
  for n in $out; do
    for f in PROPOSED PROOF; do
      awk -v n="$n" 'BEGIN{skip=0} /^(law|def) /{h=$2; sub(/[(:].*/, "", h); sub(/^Proposed\./, "", h); skip=(h==n)} !skip' $work/k/$f.bend > $work/k/$f.tmp && mv $work/k/$f.tmp $work/k/$f.bend
    done
  done
  kv=$(cd $work/k && $bend PROOF.bend --verdict 2>&1)
  print "verdict without the ${#out} out of the kernel's scope (${out}): ${kv%%$'\n'*} ($(grep -c '^law ' $work/k/PROPOSED.bend) squares)"
  [[ $kv == "ALL PROOFS CHECK"* ]] || fail=1
else
  [[ $v == "ALL PROOFS CHECK"* ]] || fail=1
fi
print "== at GHC's answers (bend/Adj.bend)"
(cd $here/../../bend && $bend Adj.bend -o $work/adj > $work/adj.build.log 2>&1) || { print "adj: build failed ($work/adj.build.log)"; exit 1 }
BEND=$bend $work/adj $work $mod | tee $work/adj.out
last=$(tail -1 $work/adj.out)
n=${${last#instances at GHC\'s answers: }%%,*}
k=${${last#*in files that check: }%%;*}
[[ $n == $k ]] || fail=1
grep -q 'check: SOME PROOFS FAIL\|verdict: SOME PROOFS FAIL' $work/adj.out && fail=1
(( fail == 0 )) && print PASS || print FAIL
exit $fail
