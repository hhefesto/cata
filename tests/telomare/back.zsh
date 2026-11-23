#!/usr/bin/env zsh
# back.zsh LAW WORK: law --package on telomare's spec output (tsp60) with
# CATA_BEND2HS=1 (G's modules in WORK/hs), no cache, into WORK;
# WORK.done: rc, seconds. Then load.zsh WORK/hs WORK-load and laws.zsh WORK.
set -u
law=${1:A} work=${2:A}
GT=$(readlink -f ~/src/cata/run/gcroot-ghc-telomare)
export BEND=$(readlink -f ~/src/cata/run/gcroot-bend)/bin/bend
unset CATA_CACHE
rm -rf $work $work-obj; mkdir -p $work $work-obj
t0=$SECONDS
(cd /tmp/ct-pf/run && CATA_BEND2HS=1 GHC="$GT/bin/ghc -i/home/hhefesto/src/cata/run/telomare/src/src -i/home/hhefesto/src/cata/prelude -XHaskell2010 -fobject-code -outputdir $work-obj" \
  nice -n 10 $law --package $work $(cat tsp60/modules.txt) > $work.log 2>&1)
print "rc $? $((SECONDS - t0)) s" > $work.done
