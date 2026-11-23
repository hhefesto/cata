#!/usr/bin/env zsh
# laws.zsh LAWOUT: tests/back/run.zsh's comparison (h against G(F(h)), GHC the
# oracle) on a law --package run's output (ledger keys tsp60/NAME.sexp).
# Each module with a laws' script: GHCi runs it against LAWOUT/hs/NAME.hs
# (with BendRt) into LAWOUT/hs/NAME.ghc; each law of an ok-law def compared.
set -u
zmodload zsh/parameter
work=${1:A}
rt=~/src/cata-ct/prelude/Back
ghc=$(readlink -f ~/src/cata/run/gcroot-ghc-telomare)/bin/ghc
${0:A:h}/tree.zsh $work/hs $work/tree
names=()
for g in $work/*.ghci(N); do
  n=${${g:t}%.ghci}
  [[ -f $work/hs/$n.hs ]] && names+=($n)
done
for n in $names; do
  while (( ${#jobstates} >= 6 )); do sleep 0.2; done
  nice -n 10 $ghc --interactive -v0 -w -ignore-dot-ghci -i$rt -i$work/tree "*$work/hs/$n.hs" +RTS -M2g -RTS < $work/$n.ghci > $work/hs/$n.ghc 2>&1 &
done
wait
T=0 S=0 R=0 D=0 M=0 X=0 L=0 N=0 O=0
for n in $names; do
  N=$((N + 1))
  out=$work/hs/$n.ghc
  if grep -q -e "$n\.hs:[0-9]*:[0-9]*: error" -e "BendRt\.hs:[0-9]*:[0-9]*: error" $out; then ld="does not load"; else ld=loads; L=$((L + 1)); fi
  oks=(${(f)"$(awk -F'\t' -v f="tsp60/$n.sexp" '$1 == f && $3 == "ok-law" {print $2}' $work/ledger.tsv)"})
  O=$((O + ${#oks}))
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
  done < <(grep "^@law " $work/$n.ghc)
  print "$n: G(F(h)) $ld; ok-law defs ${#oks}, laws $t: same $s, more defined $r, differ $d, missing $((m + x)) (script $x)"
  T=$((T + t)) S=$((S + s)) R=$((R + r)) D=$((D + d)) M=$((M + m)) X=$((X + x))
done
print "modules with laws: $N, G(F(h)) loads in GHC: $L; ok-law defs $O; laws $T: same $S, more defined $R, differ $D, missing $((M + X)) (in modules that do not load $M, refused by GHC in modules that load $X)"
