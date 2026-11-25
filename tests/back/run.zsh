#!/usr/bin/env zsh
# tests/back/run.zsh LAW WORK FILE...: bend2hs's round trip, with GHC the
# oracle: h against G(F(h)).  Each FILE is one module (no package), a .hs
# (hs-export writes WORK/ex/NAME.sexp) or an export already (NAME.sexp,
# linked into WORK/ex); law (with CATA_BEND2HS) writes F(h)
# into WORK/l, its laws' GHCi script NAME.ghci, GHC's answers for h
# NAME.ghc, and G(F(h)), bend/Back.bend's Haskell, as WORK/l/hs/NAME.hs.
# GHC then runs the same script against hs/NAME.hs (WORK/l/hs/NAME.ghc,
# with prelude/Back/BendRt.hs), and each law of a def law kept (ok-law in
# the ledger) is compared, answer for answer, with h's.
#   GHC: the ghc (law's oracle, .#ghc); HSX: hs-export; BEND: bend;
#   JOBS: GHC sessions at once (4); LAWOUT: a law run's WORK/l to reuse
#   (law is not run again)
# A module loads when GHC reports no error in hs/NAME.hs or BendRt (an
# error of the script's own lines, at a def law dropped, is not one).  A
# law is the same (G's answer is h's), more defined (h errs or runs out of
# time, G(F(h)) answers: F made a partial h total, as Bend's defs are),
# different (any other pair), or missing: its module does not load, or it
# loads but GHC refuses the law's line (G's types are not h's there).
# Prints, by module: whether G(F(h)) loads, its laws by kind; then the
# totals.  Exits 1 when an answer differs.
set -u
zmodload zsh/parameter
law=${1:A} work=${2:A}
shift 2
here=${0:A:h}
lawg=${0:A:h}/lawg.sed natg=${0:A:h}/natg.awk
rt=${here:h:h}/prelude/Back
ghc=${GHC:-ghc}
hsx=${HSX:-hs-export}
jobs=${JOBS:-4}
if [[ -n ${LAWOUT:-} ]]; then
  mkdir -p $work
  [[ $work/l -ef ${LAWOUT:A} ]] || { rm -rf $work/l; ln -s ${LAWOUT:A} $work/l }
else
  rm -rf $work/ex $work/l
  mkdir -p $work/ex $work/l
  sexps=()
  for f in "$@"; do
    if [[ $f == *.sexp ]]; then
      ln -s ${f:A} $work/ex/${f:t}; sexps+=($work/ex/${f:t}); continue
    fi
    n=${${f:t}%.hs}
    $hsx $work/ex/$n.sexp ${f:A} > $work/ex/$n.log 2>&1 && sexps+=($work/ex/$n.sexp) || print "$n: hs-export failed"
  done
  (cd $work && CATA_BEND2HS=1 nice -n 10 $law l $sexps > l.log 2>&1) || { print "law failed: $work/l.log"; exit 1 }
fi
# GHC on each G(F(h)), JOBS at a time
names=()
for g in $work/l/*.ghci(N); do
  n=${${g:t}%.ghci}
  [[ -f $work/l/hs/$n.hs ]] && names+=($n)
done
for n in $names; do
  while (( ${#jobstates} >= jobs )); do sleep 0.2; done
  nice -n 10 ${=ghc} --interactive -v0 -w -ignore-dot-ghci -i$rt -i$work/l/hs "*$work/l/hs/$n.hs" +RTS -M2g -RTS < <(sed -f $lawg $work/l/$n.ghci | awk -f $natg) > $work/l/hs/$n.ghc 2>&1 &
done
wait
# the limits of a law's call (2 s, 500 MB: Law.bend's lawRun) are h's: where
# h answers within them and G(F(h)) (interpreted, BendRt with it) does not,
# G's calls run again with 10 s and 8 GB
for n in $names; do
  o=$work/l/hs/$n.ghc
  again=$(awk 'NR == FNR { if ($1 == "@law" && $4 == "timeout") g[$2 " " $3]; next } $1 == "@law" && $4 == "ok" && ($2 " " $3) in g { print "lawRun \"" $2 "\" " $3 " " }' $o $work/l/$n.ghc)
  [[ -n $again ]] || continue
  while (( ${#jobstates} >= jobs )); do sleep 0.2; done
  print -r -- $again > $work/l/hs/$n.again
  { sed -f $lawg $work/l/$n.ghci | awk -f $natg | awk -v A=$work/l/hs/$n.again 'BEGIN { while ((getline x < A) > 0) k[++c] = x } /^lawRun "/ { for (i = 1; i <= c; i++) if (index($0, k[i]) == 1) { print; next } next } { print }' |
    sed 's/setAllocationCounter 500000000/setAllocationCounter 8000000000/; s/LawT.timeout 2000000/LawT.timeout 10000000/' |
    nice -n 10 ${=ghc} --interactive -v0 -w -ignore-dot-ghci -i$rt -i$work/l/hs "*$work/l/hs/$n.hs" +RTS -M2g -RTS > $work/l/hs/$n.ghc2 2>&1
    awk 'NR == FNR { if ($1 == "@law" && $4 != "timeout") g[$2 " " $3] = $0; next } $1 == "@law" && $4 == "timeout" && ($2 " " $3) in g { print g[$2 " " $3]; next } { print }' $work/l/hs/$n.ghc2 $o > $o.new && mv $o.new $o } &
done
wait
T=0 S=0 R=0 D=0 M=0 X=0 L=0 N=0
for n in $names; do
  N=$((N + 1))
  out=$work/l/hs/$n.ghc
  if grep -q -e "$n\.hs:[0-9]*:[0-9]*: error" -e "BendRt\.hs:[0-9]*:[0-9]*: error" $out; then ld="does not load"; else ld=loads; L=$((L + 1)); fi
  oks=(${(f)"$(awk -F'\t' -v f="ex/$n.sexp" '$1 ~ f"$" && $3 == "ok-law" {print $2}' $work/l/ledger.tsv)"})
  t=0 s=0 r=0 d=0 m=0 x=0
  while IFS= read -r line; do
    set -- ${=line}
    (( ${oks[(Ie)$2]} )) || continue
    t=$((t + 1))
    other=$(grep -F -m1 -- "@law $2 $3 " $out)
    if [[ -z $other ]]; then
      if [[ $ld == loads ]]; then x=$((x + 1)); else m=$((m + 1)); fi
    elif [[ $other == $line ]]; then s=$((s + 1))
    elif [[ ( $4 == err || $4 == timeout ) && $other == "@law $2 $3 ok "* ]]; then r=$((r + 1)); print "  more defined: $line | G: $other"
    else d=$((d + 1)); print "  differs: $line | G: $other"
    fi
  done < <(grep "^@law " $work/l/$n.ghc)
  print "$n: G(F(h)) $ld; ok-law defs ${#oks}, laws $t: same $s, more defined $r, differ $d, missing $((m + x)) (script $x)"
  T=$((T + t)) S=$((S + s)) R=$((R + r)) D=$((D + d)) M=$((M + m)) X=$((X + x))
done
print "modules with laws: $N, G(F(h)) loads in GHC: $L; laws $T: same $S, more defined $R, differ $D, missing $((M + X)) (in modules that do not load $M, refused by GHC in modules that load $X)"
(( D == 0 ))
