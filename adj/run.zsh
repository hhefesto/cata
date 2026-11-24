#!/usr/bin/env zsh
# adj/run.zsh: cata as a functor and an adjunction, proved.  bend
# --check-only, then --verdict (BendTT's kernel) on adj/PROOF.bend, and on
# adj/INT.bend, adj/LAZY.bend, adj/CATA.bend and adj/REC.bend (the model's Int, Int8,
# laziness, catamorphisms, recursion and functions as values
# against GHC's; int.zsh writes them from GHC again), and on adj/HSINT.bend
# (the prelude's own HsInt is the model's Int; hsint.zsh writes its HsInt.bend
# from what cata writes).
#   BEND names the bend; LEAN a directory holding Lean 4.34.0's lean (for
#   --verdict).  Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
cd $here
ok=1
for f in PROOF INT LAZY HSINT CATA REC; do
  c=$(BEND_NO_TELEMETRY=1 $bend $f.bend --check-only 2>&1)
  print "$f check: ${c//$'\n'/ | }"
  v=$(BEND_NO_TELEMETRY=1 $bend $f.bend --verdict 2>&1)
  print "$f verdict: ${v//$'\n'/ | }"
  [[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]] || ok=0
done
if (( ok )); then print PASS; else print FAIL; exit 1; fi
