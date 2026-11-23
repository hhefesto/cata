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
#   GHC: the ghc (law's oracle, .#ghc); HSX: hs-export; BEND: bend
# Prints, by module: whether G(F(h)) loads in GHC, and its laws the same,
# different, or missing; then the totals.  Exits 1 when an answer differs.
set -u
law=${1:A} work=${2:A}
shift 2
here=${0:A:h}
rt=${here:h:h}/prelude/Back
ghc=${GHC:-ghc}
hsx=${HSX:-hs-export}
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
T=0 S=0 D=0 M=0 L=0 N=0
for g in $work/l/*.ghci(N); do
  n=${${g:t}%.ghci}
  h=$work/l/hs/$n.hs
  [[ -f $h ]] || continue
  N=$((N + 1))
  ${=ghc} --interactive -v0 -w -ignore-dot-ghci -i$rt -i$work/l/hs "*$h" +RTS -M2g -RTS < $g > $work/l/hs/$n.ghc 2>&1
  # the module loads when GHC says nothing before its first answer
  if grep -q "^@law " $work/l/hs/$n.ghc && ! sed '/^@law /,$d' $work/l/hs/$n.ghc | grep -q "rror"; then ld=loads; L=$((L + 1)); else ld="does not load"; fi
  oks=(${(f)"$(awk -F'\t' -v f="ex/$n.sexp" '$1 ~ f"$" && $3 == "ok-law" {print $2}' $work/l/ledger.tsv)"})
  t=0 s=0 d=0 m=0
  while IFS= read -r line; do
    set -- ${=line}
    (( ${oks[(Ie)$2]} )) || continue
    t=$((t + 1))
    other=$(grep -F -m1 -- "@law $2 $3 " $work/l/hs/$n.ghc)
    if [[ -z $other ]]; then m=$((m + 1))
    elif [[ $other == $line ]]; then s=$((s + 1))
    else d=$((d + 1)); print "  differs: $line | G: $other"
    fi
  done < <(grep "^@law " $work/l/$n.ghc)
  print "$n: G(F(h)) $ld; ok-law defs ${#oks}, laws $t: same $s, differ $d, missing $m"
  T=$((T + t)) S=$((S + s)) D=$((D + d)) M=$((M + m))
done
print "modules with laws: $N, G(F(h)) loads in GHC: $L; laws $T: same $S, differ $D, missing $M"
(( D == 0 ))
