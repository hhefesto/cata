#!/usr/bin/env zsh
# The Data.Graph model (prelude/Cata/Graph.hs) against containers: Check.hs's
# 20,000 graphs of each of its four kinds, every answer the same.
#   tests/graph/run.sh
# GHC: a ghc with containers (the flake's .#ghc-telomare).
set -eu
here=${0:A:h}
cata=${here:h:h}
w=$(mktemp -d)
GHC=${GHC:-ghc}
${=GHC} -O0 -XHaskell2010 -i$cata/prelude -outputdir $w/obj -o $w/check $here/Check.hs > $w/check.log 2>&1 || { cat $w/check.log; exit 1; }
$w/check
