#!/usr/bin/env zsh
# adj/gen/cert.zsh OUT LDIR: certificates of cata's own answers.  LDIR is
# adj/gen/run.zsh's OUT/l, cata's Bend of the generated programs; for each
# one cata takes, OUT/c/cN.bend states that cata's def dN answers, at every
# input, what the model's meaning of the Haskell program answers (L.Le:
# wherever the model answers), and proves it: Gen.bend writes the statement
# and the splits of the argument's type, Cert.bend the steps where a leaf
# does not compute to the same (a split, or an induction for a fold), until
# Bend checks the file (or no step is left: OPEN, and why).  With VERDICT=1
# each proved one is then checked by the proof kernel (bend --verdict).
# With SAME=1 the statement is stronger: cata's def answers exactly what the
# model answers, an error where it errs (== instead of L.Le).  That is false
# where GHC's laziness answers and the strict model errs (cata's Bend drops
# what nothing uses, as GHC never forces it), so SAME's OPEN ones are
# either that or a search that ended.
#   BEND the bend; STEPS the most checks of a program (1500), DEPTH the
#   most steps in a row (40); LEAN a directory holding Lean 4.34.0's lean
#   (for VERDICT); ONLY some programs' numbers (all); JOBS programs at once
#   (4); BIN a directory holding gen and cert, built before
set -u
here=${0:A:h}
out=${1:A} l=${2:A}
bend=${BEND:-bend}
steps=${STEPS:-1500} depth=${DEPTH:-40}
[[ -e $out ]] && { print "$out exists"; exit 1 }
mkdir -p $out/gen $out/l $out/c $out/bin
cp $here/../Core.bend $out/; cp $here/L.bend $here/R.bend $here/S.bend $out/gen/
# (without their own laws, GHC's answers at points: dN.exK)
for f in $l/Frag<->.bend $l/Cata_Base.bend(N); do awk '/^# GHC: /{next} /^def [^ ]*\.ex[0-9]+\(\) -> /{skip=1} !skip{print} skip && /^$/{skip=0}' $f > $out/l/${f:t}; done
cp $l/HsPrelude.bend $out/l/
export BEND_NO_TELEMETRY=1
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
# MUT: a sed program that breaks cata's Bend, to see certificates fail
[[ -n ${MUT:-} ]] && sed -i -e $MUT $out/l/*.bend
if [[ -n ${BIN:-} ]]; then cp $BIN/gen $BIN/cert $out/bin/; else
  $bend $here/Gen.bend -o $out/bin/gen > $out/bin/gen.log 2>&1 && $bend $here/Cert.bend -o $out/bin/cert > $out/bin/cert.log 2>&1 || { tail -5 $out/bin/*.log; exit 1 }
fi

kimp=() ksig=()
[[ -e $out/l/Cata_Base.bend ]] && kimp=("import ../l/Cata_Base.bend as K") ksig=(K=$out/l/Cata_Base.bend)

# one program: N FragK.  A step of a fold has choices (which of cata's calls
# is the model's fold, or none): the first that leads to a checked file.
one() {
  local i=$1 m=$2 f=$out/c/c$1.bend n=0 tries=0 ch=0
  local -a saved chs
  local p=total
  grep -B1 "^def d$i(" $out/l/$m.bend | grep -q '^# partial' && p=partial
  { print -l "# cata's d$i (l/$m.bend) is the model's meaning of it, at every input" "import Base" "import ../Core.bend as C" "import ../gen/R.bend as R" "import ../gen/L.bend as L" "import ../gen/S.bend as S" "import ../l/$m.bend as D" "import ../l/HsPrelude.bend as H" "${kimp[@]}" ""; $out/bin/gen cert $i $p ${SAME:+same} } > $f
  while true; do
    tries=$((tries + 1))
    (cd $out/c && timeout 120 $bend c$i.bend --check-only > c$i.log 2>&1)
    if grep -q '^ALL PROOFS CHECK' $out/c/c$i.log; then
      print "$i $m $p proved $n steps" > $out/c/c$i.res
      if [[ -n ${VERDICT:-} ]]; then
        (cd $out/c && timeout 600 $bend c$i.bend --verdict > c$i.vlog 2>&1)
        grep -q '^ALL PROOFS CHECK' $out/c/c$i.vlog && print "$i $m $p verdict $n steps" > $out/c/c$i.res || print "$i $m $p NOVERDICT $n steps: $(head -3 $out/c/c$i.vlog | tr '\n' ' ')" > $out/c/c$i.res
      fi
      rm -f $f.*(N)
      return
    fi
    (( tries >= steps )) && { print "$i $m $p OPEN $n steps: no end" > $out/c/c$i.res; return }
    ch=0
    while true; do
      # back to the last step with a choice left, when this one has none
      if (( ch < 0 )); then
        (( n == 0 )) && { print "$i $m $p OPEN: $(tr '\n' ' ' < $f.why | cut -c1-160)" > $out/c/c$i.res; return }
        cp $f.$n $f; cp $f.$n.log $out/c/c$i.log; ch=$((chs[n] + 1)); n=$((n - 1))
      fi
      if (( n < depth )) && timeout 60 $out/bin/cert step $((n + 1)) $ch $f $out/c/c$i.log R=$out/gen/R.bend D=$out/l/$m.bend H=$out/l/HsPrelude.bend "${ksig[@]}" > $f.new 2> $f.w; then
        n=$((n + 1)); chs[$n]=$ch
        cp $f $f.$n; cp $out/c/c$i.log $f.$n.log; cp $f.new $f
        break
      fi
      [[ $ch == 0 ]] && cp $f.w $f.why
      ch=-1
    done
  done
}

awk -F'\t' '$1 ~ /Frag[0-9]+\.sexp$/ && $2 ~ /^d[0-9]+$/ && $3 != "out" {sub(/.*\//, "", $1); sub(/\.sexp/, "", $1); sub(/^d/, "", $2); print $2, $1}' $l/ledger.tsv > $out/todo
[[ -n ${ONLY:-} ]] && { awk -v o=" $ONLY " 'index(o, " " $1 " ")' $out/todo > $out/todo.1; cp $out/todo.1 $out/todo }
while read -r i m; do
  while (( ${#jobstates} >= ${JOBS:-4} )); do sleep 0.1; done
  one $i $m < /dev/null &
done < $out/todo
wait
cat $out/c/*.res | sort -n > $out/res
awk '{k = $4; sub(/:$/, "", k); c[k]++; n++} END {printf "certificates: %d programs, proved at every input %d (with the kernel'"'"'s verdict %d), open %d\n", n, c["proved"] + c["verdict"], c["verdict"], c["OPEN"] + c["NOVERDICT"]}' $out/res
grep 'OPEN\|NOVERDICT' $out/res
true
