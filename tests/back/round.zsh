#!/usr/bin/env zsh
# tests/back/round.zsh LAW LAWOUT WORK [NAME...]: the other half of the round
# trip, F(G(b)) against b.  LAWOUT is a law run with CATA_BEND2HS=1
# (tests/back/run.zsh's WORK/l): b is LAWOUT/NAME.bend, cata's Bend of h,
# and G(b) is LAWOUT/hs/NAME.hs, bend/Back.bend's Haskell of it.  For each
# NAME (default: every LAWOUT/hs/NAME.hs whose module has a laws' script),
# G(b) and BendRt.hs are exported as a package (hs-export --package) and
# law runs on them (CATA_BEND2HS unset): WORK/NAME/l holds F(G(b)) as
# WORK/NAME/l/MOD.bend and its ledger.  JOBS at a time (6).
#   GHC: the ghc; HSX: hs-export; BEND: bend
# WORK/NAME.done holds law's exit code and seconds.  Then the comparison
# (bend/Round.bend, built to WORK/round): each def of b same, differ or
# missing (WORK/round.tsv: NAME, def, status, reason), and each differing
# def's laws from b checked against F(G(b)) (bend --check-only on
# WORK/NAME/l/round_K.bend: WORK/laws.tsv).  STAGE=cmp skips the law runs
# (they are there already).
set -u
zmodload zsh/parameter
law=${1:A} lawout=${2:A} work=${3:A}
shift 3
here=${0:A:h}
rt=${here:h:h}/prelude/Back
ghc=${GHC:-ghc}
hsx=${HSX:-hs-export}
jobs=${JOBS:-6}
mkdir -p $work
names=("$@")
if (( ${#names} == 0 )); then
  for g in $lawout/hs/*.hs(N); do
    n=${${g:t}%.hs}
    [[ -f $lawout/$n.ghci ]] && names+=($n)
  done
fi
one() {
  local n=$1 d=$work/$1
  rm -rf $d; mkdir -p $d/ex $d/l $d/obj
  print -l -- "-i$rt" -XHaskell2010 -- $rt/BendRt.hs $lawout/hs/$n.hs > $d/args
  local t0=$SECONDS
  if ! $hsx --package $d/ex $d/args > $d/ex.log 2>&1; then print "hsx $? 0" > $work/$n.done; return; fi
  (cd $d && GHC="${ghc} -i$rt -fobject-code -outputdir $d/obj" CATA_BEND2HS= nice -n 10 $law --package l $(cat ex/modules.txt) > l.log 2>&1)
  print "law $? $((SECONDS - t0))" > $work/$n.done
}
if [[ ${STAGE:-all} != cmp ]]; then
  for n in $names; do
    while (( ${#jobstates} >= jobs )); do sleep 0.2; done
    one $n &
  done
  wait
fi
bend=${BEND:-bend}
# the runtime's own modules (prelude/Back: BendRt, BendPc), exported with
# every G(b): the module compared is the one that is not one of them
rtm=($rt/*.hs(N:t:r))
(cd ${here:h:h}/bend && BEND_NO_TELEMETRY=1 $bend Round.bend -o $work/round > $work/round.build.log 2>&1) || { print "round: build failed ($work/round.build.log)"; exit 1 }
: > $work/round.tsv
for n in $names; do
  d=$work/$n
  rm -f $d/l/round_*.bend(N)
  m=$(grep -v -E "/(${(j:|:)rtm})\.sexp\$" $d/ex/modules.txt 2>/dev/null | head -1)
  m=${${m:t}%.sexp}
  if [[ -z $m || ! -f $d/l/ledger.tsv ]]; then print "$n\t*\tno-run\t$(cat $work/$n.done 2>/dev/null)" >> $work/round.tsv; continue; fi
  # law writes no MOD.bend when it keeps nothing of the module: every def
  # is then missing, with the ledger's reason
  f=$d/l/$m.bend
  [[ -f $f ]] || { f=$d/l/round_none.txt; : > $f }
  $work/round $lawout/$n.bend $lawout/hs/$n.hs $f $d/l/ledger.tsv $work > $d/round.out 2>&1
  grep -v '^laws-files' $d/round.out | sed "s/^/$n\t/" >> $work/round.tsv
done
: > $work/laws.tsv
chk() {
  local f=$1
  local r=$(cd ${f:h} && BEND_NO_TELEMETRY=1 timeout 600 nice -n 10 $bend ${f:t} --check-only 2>&1 | grep -v '^Hint' | head -4 | tr '\t\n' '  ')
  print "${f:h:h:t}\t${f:t}\t$r" >> $work/laws.tsv
}
for f in $work/*/l/round_*.bend(N); do
  while (( ${#jobstates} >= jobs )); do sleep 0.2; done
  chk $f &
done
wait
# each def's verdict: same; laws (its text differs, b's laws hold of
# F(G(b))'s def: round_K is the module's K-th def that differs and has
# laws); differ (b's laws fail on it, or it has none); missing (F refused
# it: the ledger's reason).  Then each module's: missing if F refused one
# of its defs, else differ if one differs, else laws if one is equal only
# by its laws, else same.
awk -F'\t' 'NR == FNR { split($2, a, /[_.]/); r[$1 "\t" a[2]] = $3; next }
  { k = $1 "\t" n[$1] + 0 }
  $3 == "differ" && $4 == "laws" { n[$1]++; v = r[k]; print $1 "\t" $2 "\t" (v ~ /^ALL PROOFS CHECK/ ? "laws\t" $5 : "differ\t" $5 "; laws fail: " v); next }
  $3 == "differ" { print $1 "\t" $2 "\tdiffer\t" $5 "; no laws"; next }
  { print }' $work/laws.tsv $work/round.tsv > $work/defs.tsv
print -l $names > $work/names.txt
awk -F'\t' 'NR == FNR { m[$1]; next } $3 != "not-in-b" { c[$1, $3]++; d[$1]++ }
  END { for (x in m) print x "\t" (!d[x] ? "no defs" : c[x, "missing"] ? "missing" : c[x, "differ"] ? "differ" : c[x, "laws"] ? "laws" : c[x, "no-run"] ? "no-run" : "same") }' $work/names.txt $work/defs.tsv | sort > $work/modules.tsv
# --verdict on a sample of the laws' files that check: the first SAMPLE
# (40) of them
: > $work/verdict.tsv
vdt() {
  local f=$1
  local r=$(cd ${f:h} && BEND_NO_TELEMETRY=1 timeout 900 nice -n 10 $bend ${f:t} --verdict 2>&1 | grep -v '^Hint' | head -3 | tr '\t\n' '  ')
  print "${f:h:h:t}\t${f:t}\t$r" >> $work/verdict.tsv
}
for f in $(awk -F'\t' '$3 ~ /^ALL PROOFS CHECK/ {print $1 "/l/" $2}' $work/laws.tsv | sort | head -${SAMPLE:-40}); do
  while (( ${#jobstates} >= jobs )); do sleep 0.2; done
  vdt $work/$f &
done
wait
# BendRt's wrappers' rewrites as laws (law writes BendRt_rt.bend: Fold's
# fd.rt.laws), from the first module's run (BendRt is the same in every
# run)
rtf=$(print -l $work/*/l/BendRt_rt.bend(N) | head -1)
if [[ -n $rtf ]]; then
  rc=$(cd ${rtf:h} && BEND_NO_TELEMETRY=1 timeout 900 $bend BendRt_rt.bend --check-only 2>&1 | grep -v '^Hint' | head -4 | tr '\n' ' ')
  rv=$(cd ${rtf:h} && BEND_NO_TELEMETRY=1 timeout 900 $bend BendRt_rt.bend --verdict 2>&1 | grep -v '^Hint' | head -4 | tr '\n' ' ')
fi
print "modules: ${#names}"
print "defs of b: $(awk -F'\t' '$3 != "no-run"' $work/round.tsv | wc -l); by Round's comparison:"
awk -F'\t' '{print $3}' $work/round.tsv | sort | uniq -c
print "laws' files (one per differing def with laws): $(wc -l < $work/laws.tsv); by bend --check-only:"
awk -F'\t' '{print $3}' $work/laws.tsv | sed 's/^\(ALL PROOFS CHECK\|SOME PROOFS FAIL\).*/\1/' | sort | uniq -c
print -r -- "--verdict on $(wc -l < $work/verdict.tsv) of those that check:"
awk -F'\t' '{print $3}' $work/verdict.tsv | sed 's/^\(ALL PROOFS CHECK\|SOME PROOFS FAIL\).*/\1/' | sort | uniq -c
print "defs, by verdict (WORK/defs.tsv):"
awk -F'\t' '{print $3}' $work/defs.tsv | sort | uniq -c
print "modules, by verdict (WORK/modules.tsv):"
awk -F'\t' '{print $2}' $work/modules.tsv | sort | uniq -c
print "BendRt's wrapper laws ($(grep -c '^def .*\.rt(' ${rtf:-/dev/null} 2>/dev/null)): check: ${rc:-none}; verdict: ${rv:-none}"
