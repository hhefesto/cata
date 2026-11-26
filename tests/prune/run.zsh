#!/usr/bin/env zsh
# run.zsh: P.hs through hs-export, spec, prune (roots.txt: P.run) and the
# fold, and the pruned fold's P.bend told against what prune must leave out:
# R's fields unused and alsoUnused (their terms, expensive's call and
# helper's, unbuilt), Q's second field, combine's y and then mk's b (its
# only use, the where-bound cost, unused once unused is gone), and
# expensive itself, reached from nothing left.
# HSX: hs-export; SPEC, PRUNE, LAW: the binaries; GHCT: ghc-telomare's
# store path (its package db). The fold runs without GHC (no laws).
set -eu
here=${0:A:h}
w=$(mktemp -d /tmp/ct-prune.XXXXXX)
cat > $w/args <<EOF
-i$here
-XHaskell2010
-package-db
$GHCT/lib/ghc-9.10.3/lib/package.conf.d
--
$here/P.hs
EOF
mkdir $w/ex $w/sp $w/fo
$HSX --package $w/ex $w/args > $w/ex.log 2>&1
$SPEC $w/sp $(cat $w/ex/modules.txt) > $w/sp.log 2>&1
$PRUNE $here/roots.txt $w/pr $(cat $w/sp/modules.txt) | tee $w/pr.log
GHC=false $LAW --package $w/fo $(cat $w/pr/modules.txt) > $w/fo.log 2>&1
b=$w/fo/P.bend
fail=0
want() { grep -qF -- "$1" $b || { print "missing: $1"; fail=1 } }
none() { ! grep -qF -- "$1" $b || { print "left in: $1"; fail=1 } }
want 'R.R{used: HsPrelude.HsInt}'
want 'Q.Q{value: HsPrelude.HsInt}'
want 'def mk(a: HsPrelude.HsInt) -> R:'
want 'def combine(x: HsPrelude.HsInt, z: HsPrelude.HsInt)'
none 'expensive'
none 'unused'
none 'helper(b'
(( fail )) && { print "FAIL ($w)"; exit 1 }
print "ok"
