#!/usr/bin/env zsh
# tests/hs/bin/run.zsh SPEC LAW WORK: Telc.hs and the Binary model
# (prelude/Cata/Binary.hs) as one package, as telomare's is: hs-export
# (HSX), spec, law --package with CATA_BEND2HS, GHC (GHCT: one with binary,
# utf8-string, filepath and mtl, the telomare GHC) the oracle; prints the
# ledger by kind and tests/telomare/laws.zsh's totals.
#   HSX: hs-export; GHCT: that GHC's directory; BEND: bend
set -u
here=${0:A:h}
spec=${1:A} law=${2:A} work=${3:A}
pre=${here:h:h:h}/prelude
GT=${GHCT:?GHCT: the telomare GHC}
rm -rf $work; mkdir -p $work/ex $work/o $work/l
{ print -- "-i$here"; print -- "-i$pre"; print -- "-XHaskell2010"; print -- "-package-db"; print -- "$GT/lib/ghc-9.10.3/lib/package.conf.d"; print -- "--"; print -- "$pre/Cata/Binary.hs"; print -- "$here/Telc.hs" } > $work/args
${HSX:-hs-export} --package $work/ex $work/args > $work/ex.log 2>&1 || { tail -5 $work/ex.log; exit 1 }
$spec $work/o $(cat $work/ex/modules.txt) > $work/o.log 2>&1 || { tail -5 $work/o.log; exit 1 }
cd $work
CATA_BEND2HS=1 GHC="$GT/bin/ghc -i$here -i$pre -XHaskell2010 -fobject-code -outputdir $work/obj" $law --package l $(sed "s#^$work/##" o/modules.txt) > l.log 2>&1
print "law rc $?"
awk -F'\t' '{print $3}' l/ledger.tsv | sort | uniq -c | sort -rn | tr -s ' \n' ' '; print
PFX=o GHCI=$GT/bin/ghc $here/../../telomare/laws.zsh $work/l 2>&1 | tail -1
