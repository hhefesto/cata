#!/usr/bin/env zsh
# Telomare's parser in Bend against GHC's: the skeleton of each file's parse
# (Skel.hs: items, names, spans; or the error's text) from telomare's
# Telomare.Parse under GHC and from cata's Bend of it, the same.
#   tests/telomare/run.sh SRC PKG FILE.tel...
# SRC: telomare's source (its src/ under it); PKG: a law/fold --package
# output holding Telomare_Parse.bend and the modules before it.
# GHC: a ghc with telomare's packages (the flake's .#ghc-telomare); BEND.
# One Bend run per file: Bend's interpreter overflows its machine stack on
# the text of many at once.
set -eu
here=${0:A:h}
src=$1 pkg=$2
shift 2
w=$(mktemp -d)
GHC=${GHC:-ghc}
BEND=${BEND:-bend}
${=GHC} -O0 -XHaskell2010 -i$src/src -outputdir $w/obj -o $w/skel $here/Skel.hs > $w/ghc.log 2>&1 || { cat $w/ghc.log; exit 1; }
cp $pkg/*.bend $w/
n=0 bad=0
for f in $@; do
  n=$((n + 1))
  {
    cat $here/skel.bend.part
    print '\ndef main() -> IO(Unit):\n  IO.print(String.from_list('
    $w/skel --bend ${f:t} $f
    print '))'
  } > $w/main.bend
  # IO.print ends the text with a newline
  { $w/skel ${f:t} $f; print } > $w/ghc.$n.txt
  $BEND $w/main.bend > $w/bend.$n.txt 2>&1 || true
  if ! cmp -s $w/ghc.$n.txt $w/bend.$n.txt; then
    bad=$((bad + 1))
    print "differ: ${f:t} ($w/ghc.$n.txt $w/bend.$n.txt)"
    diff $w/ghc.$n.txt $w/bend.$n.txt | head -10
  fi
done
if [ $bad = 0 ]; then
  print "Telomare.Parse: $n files, the same skeleton as GHC's"
else
  print "Telomare.Parse: $bad of $n files differ"
  exit 1
fi
