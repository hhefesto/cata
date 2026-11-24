#!/usr/bin/env zsh
# adj/int.zsh: write INT.bend from GHC's Int (IntGhc.hs) and check it
# against the model's Int (Core.bend), --check-only then --verdict.
#   GHC names a directory holding runghc; BEND the bend; LEAN a directory
#   holding Lean 4.34.0's lean (for --verdict).  Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
[[ -n ${GHC:-} ]] && export PATH=$GHC:$PATH
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
cd $here
runghc IntGhc.hs > INT.bend || { print FAIL: runghc; exit 1 }
c=$(BEND_NO_TELEMETRY=1 $bend INT.bend --check-only 2>&1)
print "check: ${c//$'\n'/ | }"
v=$(BEND_NO_TELEMETRY=1 $bend INT.bend --verdict 2>&1)
print "verdict: ${v//$'\n'/ | }"
if [[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]]; then print PASS; else print FAIL; exit 1; fi
