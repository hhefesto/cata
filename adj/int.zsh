#!/usr/bin/env zsh
# adj/int.zsh: write INT.bend from GHC's Int and Int8 (IntGhc.hs),
# LAZY.bend from GHC's laziness (LazyGhc.hs) and CATA.bend from GHC's
# catamorphisms (CataGhc.hs: recursion-schemes), and check each against the
# model (Core.bend), --check-only then --verdict.
#   GHC names a directory holding runghc (with recursion-schemes: the
#   telomare GHC); BEND the bend; LEAN a directory
#   holding Lean 4.34.0's lean (for --verdict).  Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
[[ -n ${GHC:-} ]] && export PATH=$GHC:$PATH
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
cd $here
runghc IntGhc.hs > INT.bend || { print FAIL: runghc IntGhc.hs; exit 1 }
runghc LazyGhc.hs > LAZY.bend || { print FAIL: runghc LazyGhc.hs; exit 1 }
runghc CataGhc.hs > CATA.bend || { print FAIL: runghc CataGhc.hs; exit 1 }
ok=1
for f in INT LAZY CATA; do
  c=$(BEND_NO_TELEMETRY=1 $bend $f.bend --check-only 2>&1)
  print "$f check: ${c//$'\n'/ | }"
  v=$(BEND_NO_TELEMETRY=1 $bend $f.bend --verdict 2>&1)
  print "$f verdict: ${v//$'\n'/ | }"
  [[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]] || ok=0
done
if (( ok )); then print PASS; else print FAIL; exit 1; fi
