#!/usr/bin/env zsh
# tests/square/run.zsh LAWOUT XMONAD_BEND [WORK]: the squares of
# tests/square/xmonad (cata's XMonad.StackSet against xmonad-bend's hand
# port) checked and then rechecked with BendTT's kernel.
#   LAWOUT: a law run's OUT on xmonad-0.18.1 (tests/xmonad/run.zsh's OUT/l),
#           which holds XMonad_StackSet.bend and HsPrelude.bend
#   XMONAD_BEND: a checkout of xmonad-bend (StackSet.bend, Num.bend)
#   WORK: a new directory (default: a mktemp one); the files are copied in,
#         nothing is written to LAWOUT or XMONAD_BEND
# BEND names the bend; LEAN a directory holding Lean 4.34.0's lean (for
# --verdict). Then a mutant: sq.swapUp_q paired with W.Stack.focusUp, not
# W.Stack.swapUp; the proofs must fail on it. Prints each verdict, PASS or
# FAIL.
set -u
here=${0:A:h}
lawout=${1:A} xb=${2:A} work=${3:-$(mktemp -d /tmp/ct-square.XXXXXX)}
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
mkdir -p $work/l $work/xb $work/m/l $work/m/xb
cp $lawout/*.bend $work/l/
cp $xb/*.bend $work/xb/
cp $here/xmonad/PROPOSED.bend $here/xmonad/PROOF.bend $work/
fail=0
c=$(cd $work && BEND_NO_TELEMETRY=1 $bend PROOF.bend --check-only 2>&1)
print "check:   ${c%%$'\n'*}"
[[ $c == "ALL PROOFS CHECK"* ]] || { print $c | head -20; fail=1 }
v=$(cd $work && BEND_NO_TELEMETRY=1 $bend PROOF.bend --verdict 2>&1)
print "verdict: ${v//$'\n'/ | }"
print "squares: $(grep -c '^law ' $work/PROPOSED.bend)"
# the kernel's verdict on the squares it takes: all but those it calls out
# of scope (each a law and its proof, dropped from a copy)
out=(${(f)"$(print -r -- $v | sed -n 's/^- PROPOSED\.\(sq\.[A-Za-z0-9_.]*\): .*/\1/p')"})
mkdir -p $work/k/l $work/k/xb
cp $work/l/*.bend $work/k/l/; cp $work/xb/*.bend $work/k/xb/
cp $work/PROPOSED.bend $work/PROOF.bend $work/k/
for n in $out; do
  for f in PROPOSED PROOF; do
    awk -v n="$n" 'BEGIN{skip=0} /^(law|def) /{h=$2; sub(/[(:].*/, "", h); sub(/^Proposed\./, "", h); skip=(h==n)} !skip' $work/k/$f.bend > $work/k/$f.tmp && mv $work/k/$f.tmp $work/k/$f.bend
  done
done
kv=$(cd $work/k && BEND_NO_TELEMETRY=1 $bend PROOF.bend --verdict 2>&1)
print "verdict without the ${#out} out of the kernel's scope (${out}): ${kv%%$'\n'*} ($(grep -c '^law ' $work/k/PROPOSED.bend) squares)"
[[ $kv == "ALL PROOFS CHECK"* ]] || fail=1
# the mutant: one pairing wrong
cp $lawout/*.bend $work/m/l/
cp $xb/*.bend $work/m/xb/
cp $work/PROOF.bend $work/m/
sed 's/W\.Stack\.swapUp(A, phi\.stack(A, s))/W.Stack.focusUp(A, phi.stack(A, s))/' $work/PROPOSED.bend > $work/m/PROPOSED.bend
if cmp -s $work/PROPOSED.bend $work/m/PROPOSED.bend; then print "mutant: not made"; fail=1; fi
mc=$(cd $work/m && BEND_NO_TELEMETRY=1 $bend PROOF.bend --check-only 2>&1)
print "mutant (swapUp_q paired with focusUp): ${mc%%$'\n'*}"
[[ $mc == "SOME PROOFS FAIL"* ]] || fail=1
(( fail == 0 )) && print PASS || print FAIL
exit $fail
