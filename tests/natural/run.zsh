#!/usr/bin/env zsh
# tests/natural/run.zsh LAWOUT [WORK]: naturality on a law run's output.
#   LAWOUT: the OUT of `law --package OUT ...` on telomare, run with
#           CATA_BEND2HS=1 (so OUT/hs holds G's modules); nothing is
#           written there
#   WORK: a new directory (default: a mktemp one)
# 1. Copies.hs on OUT/hs: the specialiser's copies of each def, how many
#    are one program once their types are erased (and once the copies they
#    call are named by their def alone: a dictionary's methods).
# 2. PROPOSED.bend's laws (a copied def once, polymorphic; a law proved
#    once; a copy as its instance), with bend --check-only and --verdict.
# GHC names the ghc; BEND the bend; LEAN a directory holding Lean 4.34.0's
# lean (for --verdict).  Prints PASS or FAIL.
set -u
here=${0:A:h}
out=${1:A} work=${2:-$(mktemp -d /tmp/ct-natural.XXXXXX)}
bend=${BEND:-bend}
ghc=${GHC:-ghc}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
mkdir -p $work/l $work/o
fail=0
if [[ -d $out/hs ]]; then
  ${=ghc} -O1 -v0 -outputdir $work/o -o $work/copies $here/Copies.hs && $work/copies $out/hs > $work/copies.txt
  print "copies: $(tail -1 $work/copies.txt)"
else
  print "copies: $out/hs missing (run law with CATA_BEND2HS=1)"; fail=1
fi
for f in $out/*.bend(N); do
  [[ $f == *_all.bend || $f == *_try.bend ]] || cp $f $work/l/
done
cp $here/PROPOSED.bend $here/PROOF.bend $work/
c=$(cd $work && BEND_NO_TELEMETRY=1 $bend PROOF.bend --check-only 2>&1)
print "check:   ${c%%$'\n'*}"
[[ $c == "ALL PROOFS CHECK"* ]] || { print $c | head -20; fail=1 }
v=$(cd $work && BEND_NO_TELEMETRY=1 $bend PROOF.bend --verdict 2>&1)
print "verdict: ${v//$'\n'/ | }"
[[ $v == "ALL PROOFS CHECK"* ]] || fail=1
print "laws: $(grep -c '^law ' $work/PROPOSED.bend)"
(( fail == 0 )) && print PASS || print FAIL
exit $fail
