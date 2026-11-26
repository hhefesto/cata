#!/usr/bin/env zsh
# run.zsh PKG: Check.bend on PKG's HsPrelude as it ran with Nat integers
# (Nat.bend: run-prelude with HsMapTree.bend alone) and as it runs now
# (Big.bend: all of prelude/run), then Check's answers past 2^48 against
# bc's (bc from the flake's nixpkgs). BEND: bend; CC: clang (Check
# runs native).
set -eu
here=${0:A:h} root=${0:A:h}/../..
BEND=${BEND:-bend}
w=$(mktemp -d /tmp/ct-ints.XXXXXX)
mkdir $w/pkg
cp $1/HsPrelude.bend $w/pkg/
RUN_PARTS=$root/prelude/run/HsMapTree.bend zsh $root/tools/run-prelude.zsh $w/pkg $w/nat
cp $w/nat/HsPrelude.bend $w/Nat.bend
zsh $root/tools/run-prelude.zsh $w/pkg $w/run
cp $w/run/HsPrelude.bend $w/Big.bend
cp $here/Check.bend $w/
cd $w
$BEND Check.bend -o check.c
${CC:-clang} -O1 -w -o check check.c -lm -lpthread -ldl
./check > out.txt
head -2 out.txt
# each big line: a b c d e : x y x+y x-y x*y quot rem div mod cmp
{
  print -r 'define fd(a, b) { auto q; q = a / b; if (a % b != 0) { if (a * b < 0) { q = q - 1 } }; return (q) }'
  print -r 'define cm(a, b) { if (a < b) { return (0) }; if (a == b) { return (1) }; return (2) }'
  grep -v '^$' out.txt | tail -n +3 | while read a b c d e rest; do
    print "x = $a * $b * $c; y = $d * $e"
    print -r 'print x, " ", y, " ", x + y, " ", x - y, " ", x * y, " ", x / y, " ", x % y, " ", fd(x, y), " ", x - fd(x, y) * y, " ", cm(x, y), "\n"'
  done
  print -r 'print 2^130 - 1, "\n"'
} > bc.in
BC_LINE_LENGTH=0 nix shell --inputs-from $root nixpkgs#bc -c bc -q bc.in > bc.out < /dev/null
grep -v '^$' out.txt | tail -n +3 | sed 's/^.* : //' > big.txt
n=$(wc -l < big.txt)
head -n $n bc.out | diff big.txt - > big.diff && print "$n big cases: bc agrees" || print "$n big cases: $(grep -c '^<' big.diff) differ from bc ($w/big.diff)"
[[ $(sed -n 2p out.txt) == "2^130 - 1 = $(tail -1 bc.out), back to 0 in 130 steps" ]] && print "2^130 - 1: bc agrees, back in 130" || print "2^130 - 1: differs ($w/out.txt)"
