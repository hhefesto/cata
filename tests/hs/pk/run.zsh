#!/usr/bin/env zsh
# tests/hs/pk/run.zsh SPEC LAW WORK: this directory's modules as one package (hs-export
# --package, spec, law --package, the way back): the ledger, then G(F(h))'s laws
# against h's.
#   HSX: hs-export; GHCT: a GHC with the packages Cata.Base's model needs (the
#   telomare one); BEND: bend
set -u
here=${0:A:h} top=${0:A:h:h:h:h}
spec=${1:A} law=${2:A} w=${3:A}
cd /  # GHCi looks in the working directory first: the source of a module there, not its G(F(h))
rm -rf $w; mkdir -p $w/ex $w/o $w/l $w/obj
print -l -- "-i$here" "-i$top/prelude" -XHaskell2010 -package-db $GHCT/lib/ghc-9.10.3/lib/package.conf.d -- $top/prelude/Cata/Base.hs $top/prelude/Cata/Parsec.hs $here/*.hs > $w/args
${HSX:-hs-export} --package $w/ex $w/args > $w/ex.log 2>&1 || { tail -5 $w/ex.log; exit 1 }
$spec $w/o $(cat $w/ex/modules.txt) > $w/o.log 2>&1 || { tail -5 $w/o.log; exit 1 }
(cd $w && CATA_BEND2HS=1 GHC="$GHCT/bin/ghc -i$here -i$top/prelude -XHaskell2010 -fobject-code -outputdir $w/obj" $law --package l $(sed "s#^$w/##" o/modules.txt) > l.log 2>&1)
awk -F'\t' '$1 !~ /Cata_/ {print $2, $3, $4}' $w/l/ledger.tsv
PFX=o GHCI=$GHCT/bin/ghc $top/tests/telomare/laws.zsh $w/l 2>&1 | tail -1
