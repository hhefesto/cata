#!/usr/bin/env zsh
# tests/square/xmonad/wsmap.zsh LAWOUT XMONAD_BEND WORK: what the two
# squares BendTT's kernel calls out of its scope (sq.wss.lemma and
# sq.workspaces: "a template argument that depends on a run-time value")
# need, tried by hand on copies.  cata's XMonad.StackSet writes workspaces
# with template type parameters (~I ..) and maps workspace over the visible
# screens as hs.map(~.., ~x_1 => workspace(..), ..), a lambda as a template
# argument.  The copies here: a first-order copy of hs.map at that function
# (wsmap, as the specialiser's rule 15 copies foldr and concatMap at their
# known functions), and workspaces' type parameters erased (-I ..), with the
# squares naming wsmap and calling workspaces without the ~.  Then bend
# --check-only and --verdict on all 17 squares.  Nothing is written to
# LAWOUT or XMONAD_BEND.  BEND names the bend; LEAN a directory holding
# Lean 4.34.0's lean.  Prints the two answers and PASS when both check.
set -u
here=${0:A:h}
lawout=${1:A} xb=${2:A} work=${3:A}
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
export BEND_NO_TELEMETRY=1
mkdir -p $work/l $work/xb
cp $lawout/*.bend $work/l/
cp $xb/*.bend $work/xb/
cp $here/PROPOSED.bend $here/PROOF.bend $work/
f=$work/l/XMonad_StackSet.bend
perl -0pi -e 's/def workspaces\(~I: Data, ~L: Data, ~A: Data, ~S: Data, ~Sd: Data, (\+s: StackSet<I, L, A, S, Sd>\) -> List<&2, Workspace<I, L, A>>:\n  Con\{workspace\(I, L, A, S, Sd, current\(I, L, A, S, Sd, s\)\), List\.append\(&2, Workspace<I, L, A>, )hs\.map\(~Screen<I, L, A, S, Sd>, ~Workspace<I, L, A>, ~x_1 => workspace\(I, L, A, S, Sd, x_1\), visible\(I, L, A, S, Sd, s\)\)/def wsmap(-I: Data, -L: Data, -A: Data, -S: Data, -Sd: Data, xs: List<&2, Screen<I, L, A, S, Sd>>) -> List<&2, Workspace<I, L, A>>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case h <> t:\n      workspace(I, L, A, S, Sd, h) <> wsmap(I, L, A, S, Sd, t)\n\ndef workspaces(-I: Data, -L: Data, -A: Data, -S: Data, -Sd: Data, $1wsmap(I, L, A, S, Sd, visible(I, L, A, S, Sd, s))/s' $f
grep -q '^def wsmap' $f || { print "the copy was not made: $f has another workspaces"; exit 1 }
sed -i 's/F\.hs\.map(~F\.Screen<I, L, A, S, D>, ~F\.Workspace<I, L, A>, ~x_1 => F\.workspace(I, L, A, S, D, x_1), \([vt]\))/F.wsmap(I, L, A, S, D, \1)/; s/F\.workspaces(~I, ~L, ~A, ~S, ~D, s)/F.workspaces(I, L, A, S, D, s)/' $work/PROPOSED.bend $work/PROOF.bend
c=$(cd $work && $bend PROOF.bend --check-only 2>&1)
print "check:   ${c//$'\n'/ | }"
v=$(cd $work && $bend PROOF.bend --verdict 2>&1)
print "verdict: ${v//$'\n'/ | } ($(grep -c '^law ' $work/PROPOSED.bend) squares)"
[[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]] && { print PASS; exit 0 }
print FAIL; exit 1
