#!/usr/bin/env zsh
# BendRt's HsPc (prelude/Back/BendPc.hs, the Haskell meaning bend2hs gives
# HsPrelude.HsPc) against megaparsec: Rt.hs runs Unit.bend.part's 28 parsers
# on it, Oracle.hs the same parsers on megaparsec; the two texts the same.
#   tests/pc/rt.sh        (GHC: a ghc with megaparsec, the flake's .#ghc-telomare)
set -eu
here=${0:A:h}
cata=${here:h:h}
w=$(mktemp -d)
GHC=${GHC:-ghc}
${=GHC} -XHaskell2010 -outputdir $w/o1 -o $w/oracle $here/Oracle.hs > $w/oracle.log 2>&1 || { cat $w/oracle.log; exit 1; }
${=GHC} -XHaskell2010 -i$cata/prelude/Back -outputdir $w/o2 -o $w/rt $here/Rt.hs > $w/rt.log 2>&1 || { cat $w/rt.log; exit 1; }
$w/oracle > $w/oracle.txt
$w/rt > $w/rt.txt
if cmp -s $w/oracle.txt $w/rt.txt; then
  print "BendPc: 28 parsers, the same as megaparsec"
  rm -rf $w
else
  print "BendPc differs from megaparsec ($w/oracle.txt, $w/rt.txt)"
  exit 1
fi
