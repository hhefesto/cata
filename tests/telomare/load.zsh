#!/usr/bin/env zsh
# load.zsh HSDIR WORK: G's modules as one package: GHC --make -fno-code
# -fkeep-going on all of them at once (each finds the others by name, see
# tree.zsh), WORK/ghc.log. Prints per module its own errors (cross-module:
# a name of the package's still written as BendRt's B'/b' Telomare_ or
# Cata_; parse errors) and whether GHC took it (a module whose import
# failed is skipped), then the totals.
set -u
hs=${1:A} work=${2:A}
G=$(readlink -f ~/src/cata/run/gcroot-ghc-telomare)/bin/ghc
RT=~/src/cata-ct/prelude/Back
rm -rf $work; mkdir -p $work/o
${0:A:h}/tree.zsh $hs $work/tree
files=($work/tree/**/*.hs(@))
timeout 1800 nice -n 10 $G --make -fno-code -fkeep-going -j4 -w -i$RT -i$work/tree -outputdir $work/o $files > $work/ghc.log 2>&1
T=0 L=0
for f in $files; do
  rel=${f#$work/tree/}; n=${${rel%.hs}//\//_}
  ne=$(grep -c "^$f:[0-9]*:[0-9]*: error" $work/ghc.log)
  nx=$(grep -A2 "^$f:[0-9]*:[0-9]*: error" $work/ghc.log | grep -c "‘[bB]'\(Telomare\|Cata\)_")
  np=$(grep -A1 "^$f:[0-9]*:[0-9]*: error" $work/ghc.log | grep -c 'parse error')
  T=$((T + 1)); st=ok

  (( ne == 0 )) && L=$((L + 1))
  print "$n own-errors=$ne cross=$nx parse=$np"
done
print "modules $T, without errors of their own $L"
print "modules GHC took (all their imports took): $(grep -c 'Compiling' $work/ghc.log)"
