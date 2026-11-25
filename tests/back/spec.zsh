#!/usr/bin/env zsh
# tests/back/spec.zsh SPEC LAW WORK FILE.sexp...: modules alone (hs1003's),
# each through the specialiser with cata's model Cata.Base as a package of
# two, then law --package and the way back, the laws run against G(F(h)).
#   GHCT: a GHC with the packages Cata.Base's model needs; BEND: bend; CB:
#   Cata.Base's export; JOBS: modules at once (4); TMO: seconds a module may
#   take (1200); CATA_CACHE: law's cache (Cata.Base's check is the same in
#   every package)
# WORK/m/NAME is a module's work; WORK/ledger.tsv the modules' own rows
# (the model's and the copies' out); the totals are printed.
set -u
zmodload zsh/parameter
ulimit -s unlimited
spec=${1:A} law=${2:A} w=${3:A}
shift 3
top=${0:A:h:h:h}
cb=${CB:A}
export CATA_CACHE=${CATA_CACHE:-$w/cache}
mkdir -p $w/m $CATA_CACHE
one() {
  local f=${1:A} n=${${1:t}%.sexp}; local d=$w/m/$n
  rm -rf $d; mkdir -p $d/o $d/l
  nice -n 10 timeout 300 $spec $d/o $cb $f > $d/o.log 2>&1 || { print "spec failed" > $d/failed; return }
  (cd $d && CATA_BEND2HS=1 GHC="$GHCT/bin/ghc -i$top/prelude" nice -n 10 timeout ${TMO:-1200} $law --package l o/Cata_Base.sexp o/$n.sexp > l.log 2>&1) || { print "law failed" > $d/failed; return }
  rm -f $d/l/Cata_Base.ghci
  (cd / && PFX=o GHCI=$GHCT/bin/ghc $top/tests/telomare/laws.zsh $d/l > $d/laws.out 2>&1)
}
for f in $@; do
  while (( ${#jobstates} >= ${JOBS:-4} )); do sleep 0.2; done
  one $f &
done
wait
cat $w/m/*/l/ledger.tsv | awk -F'\t' '$1 !~ /Cata_Base/' > $w/ledger.tsv
awk -F'\t' '{k=($2 ~ /__/) ? "copies" : "defs"; c[k " " $3]++} END {for (x in c) print x, c[x]}' $w/ledger.tsv | LC_ALL=C sort
for d in $w/m/*(/); do [[ -f $d/failed ]] && print "${d:t}: $(<$d/failed)"; done
for d in $w/m/*(/); do [[ -f $d/laws.out ]] && tail -1 $d/laws.out; done | awk '{for (i=1;i<NF;i++) { if ($i=="laws:") m+=$(i+1); if ($i=="GHC:") g+=$(i+1); if ($i=="defs") o+=$(i+1); if ($i=="same") s+=$(i+1); if ($i=="defined") r+=$(i+1); if ($i=="differ") d+=$(i+1); if ($i=="missing") x+=$(i+1) }} END {print "modules with laws " m ", G(F(h)) loads " g "; ok-law defs " o "; same " s ", more defined " r ", differ " d ", missing " x}'
