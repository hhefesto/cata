#!/usr/bin/env zsh
# run.zsh TELO OUT: telomare master's library (TELO, a checkout; 11-25:
# 4e97040) through cata as one program, tictactoe's sized route by hand
# (SizedBatch.bend: runSized's compile, then evalLoop): hs-export with the
# prelude's Cata modules, spec, prune from SizedBatch.roots, the fold (no
# GHC: no laws), run-prelude, the fronts; OUT/run/sbatch is the program.
#
#   cd OUT/run; ulimit -s unlimited; ./sbatch tictactoe.tel < MOVES
#
# prints what `telomare tictactoe.tel` prints for MOVES (11-25: games
# 12457, 519372846 and 112x39, against GHC's).
# HSX: hs-export; SPEC, PRUNE, LAW: the binaries; GHCT: ghc-telomare's
# store path (its package db); BEND: bend; CC: clang. CATA_CACHE as law's.
set -eu
here=${0:A:h} root=${0:A:h}/../../..
telo=${1:A} out=${2:A}
mkdir -p $out/ex $out/sp $out/fo
{
  print -- -i$telo/src
  print -- -i$root/prelude
  print -- -XHaskell2010
  print -- -package-db
  print -- $GHCT/lib/ghc-9.10.3/lib/package.conf.d
  print -- --
  print -l $root/prelude/Cata/{Base,Parsec,Graph,Binary}.hs
  print -l $telo/src/Telomare/**/*.hs
} > $out/args
$HSX --package $out/ex $out/args > $out/ex.log 2>&1
$SPEC $out/sp $(cat $out/ex/modules.txt) > $out/sp.log 2>&1
$PRUNE $here/SizedBatch.roots $out/pr $(cat $out/sp/modules.txt) > $out/pr.log 2>&1
GHC=false $LAW --package $out/fo $(cat $out/pr/modules.txt) > $out/fo.log 2>&1
zsh $root/tools/run-prelude.zsh $out/fo $out/run
cp $here/*.bend $out/run/
cp $telo/Prelude.tel $telo/tictactoe.tel $out/run/
cd $out/run
${BEND:-bend} SizedBatch.bend -o sbatch.c
${CC:-clang} -O1 -w -o sbatch sbatch.c -lm -lpthread -ldl
print "built $out/run/sbatch"
