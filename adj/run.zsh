#!/usr/bin/env zsh
# adj/run.zsh: cata as a functor and an adjunction, proved.  bend
# --check-only, then --verdict (BendTT's kernel) on adj/PROOF.bend, and on
# adj/INT.bend and adj/LAZY.bend (the model's Int, Int8 and laziness
# against GHC's; int.zsh writes them from GHC again).
#   BEND names the bend; LEAN a directory holding Lean 4.34.0's lean (for
#   --verdict).  Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
cd $here
ok=1
for f in PROOF INT LAZY; do
  c=$(BEND_NO_TELEMETRY=1 $bend $f.bend --check-only 2>&1)
  print "$f check: ${c//$'\n'/ | }"
  v=$(BEND_NO_TELEMETRY=1 $bend $f.bend --verdict 2>&1)
  print "$f verdict: ${v//$'\n'/ | }"
  [[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]] || ok=0
done
if (( ok )); then print PASS; else print FAIL; exit 1; fi
