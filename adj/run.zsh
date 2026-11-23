#!/usr/bin/env zsh
# adj/run.zsh: cata as a functor and an adjunction, proved.  bend
# --check-only, then --verdict (BendTT's kernel) on adj/PROOF.bend.
#   BEND names the bend; LEAN a directory holding Lean 4.34.0's lean (for
#   --verdict).  Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
cd $here
c=$(BEND_NO_TELEMETRY=1 $bend PROOF.bend --check-only 2>&1)
print "check: ${c//$'\n'/ | }"
v=$(BEND_NO_TELEMETRY=1 $bend PROOF.bend --verdict 2>&1)
print "verdict: ${v//$'\n'/ | }"
if [[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]]; then print PASS; else print FAIL; exit 1; fi
