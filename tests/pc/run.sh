#!/usr/bin/env zsh
# Rule 16's checks of the megaparsec port (README, "Parsers").
#   tests/pc/run.sh HSPRELUDE
# 1. The model (prelude/Cata/Parsec.hs) against megaparsec: tests/hs/Pc.hs's
#    grammar run on 4004 inputs with megaparsec's combinators and with the
#    model's (PcM, the same module with its imports swapped), every answer
#    (errorBundlePretty's text included) the same.
# 2. HsPrelude's HsPc (prelude/HsPc.bend, in HSPRELUDE: a fold-written
#    HsPrelude.bend) against megaparsec: Oracle.hs's 28 parsers and inputs,
#    Unit.bend.part the same in Bend, their texts the same.
# GHC: a ghc with megaparsec (the flake's .#ghc-telomare); BEND: the bend.
set -eu
here=${0:A:h}
cata=${here:h:h}
w=$(mktemp -d)
GHC=${GHC:-ghc}
BEND=${BEND:-bend}
sed -e 's/^module Pc where/module PcM where/' \
    -e 's/^import Text.Megaparsec (Parsec, Pos, between, choice, eof, errorBundlePretty,/import Cata.Parsec (lineFold, many, manyTill, sepBy, sepBy1, skipBlockCommentNested, some, space)\nimport Text.Megaparsec (Parsec, Pos, between, choice, eof, errorBundlePretty,/' \
    -e 's/^                        getOffset, many, manyTill, notFollowedBy, optional,/                        getOffset, notFollowedBy, optional,/' \
    -e 's/^                        runParser, satisfy, sepBy, sepBy1, some, try, unPos,/                        runParser, satisfy, try, unPos,/' \
    -e 's/L\.space /space /g; s/L\.lineFold /lineFold /; s/L\.skipBlockCommentNested /skipBlockCommentNested /' \
    $cata/tests/hs/Pc.hs > $w/PcM.hs
${=GHC} -O0 -XHaskell2010 -i$w -i$cata/tests/hs -i$cata/prelude -outputdir $w/obj -o $w/model $here/Model.hs > $w/model.log 2>&1 || { cat $w/model.log; exit 1; }
$w/model
${=GHC} -XHaskell2010 -outputdir $w/obj2 -o $w/oracle $here/Oracle.hs > $w/oracle.log 2>&1 || { cat $w/oracle.log; exit 1; }
$w/oracle > $w/oracle.txt
cat $1 $here/Unit.bend.part > $w/unit.bend
$BEND $w/unit.bend > $w/unit.txt
# Bend writes NUL as \0 where Haskell's show writes \NUL
sed 's/\\NUL/\\0/g' $w/oracle.txt | cmp - $w/unit.txt && print "HsPc: 28 parsers, the same as megaparsec"
