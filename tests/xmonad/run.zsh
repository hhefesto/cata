#!/usr/bin/env zsh
# A Hackage package through cata as a package: hs-export, spec, survey and
# law, the ledger's counts at the end.
#   tests/xmonad/run.zsh SRC OUT SPEC LAW [SURVEY]
# SRC: the unpacked package (its src/ holds the modules); OUT: a new
# directory.  GHC: a ghc whose package db has the package's dependencies
# (the flake's .#ghc-xmonad); HSX: hs-export; BEND.  Paths_NAME, which cabal
# writes, comes from a stub in OUT/stub.
set -u
src=${1:A} out=${2:A} spec=${3:A} law=${4:A} survey=${5:-}
GHCD=${GHCD:?the ghc-with-packages directory (.#ghc-xmonad)}
HSX=${HSX:?hs-export}
pdb=$(print $GHCD/lib/ghc-*/lib/package.conf.d)
name=${${src:t}%-[0-9.]*}
ver=${${src:t}##*-}
prelude=${0:A:h:h:h}/prelude
mkdir -p $out/stub $out/ex $out/o $out/l
print "module Paths_$name (version) where\nimport Data.Version (Version, makeVersion)\nversion :: Version\nversion = makeVersion [${ver//./,}]" > $out/stub/Paths_$name.hs
{
  print -- "-i$src/src"
  print -- "-i$out/stub"
  print -- "-i$prelude"
  print -- "-XHaskell2010"
  print -- "-package-db"
  print -- "$pdb"
  print -- "--"
  print -- "$prelude/Cata/Base.hs"
  print -- "$out/stub/Paths_$name.hs"
  find $src/src -name '*.hs' | sort
} > $out/args
t0=$SECONDS
$HSX --package $out/ex $out/args > $out/ex.log 2>&1 || { print "hs-export failed: $out/ex.log"; tail -20 $out/ex.log; exit 1 }
print "hs-export: $(wc -l < $out/ex/modules.txt) modules, $((SECONDS - t0))s"
t0=$SECONDS
$spec $out/o $(cat $out/ex/modules.txt) > $out/o.log 2>&1 || { print "spec failed: $out/o.log"; tail -20 $out/o.log; exit 1 }
print "spec: $((SECONDS - t0))s"
if [ -n "$survey" ]; then
  $survey --package $out/survey.tsv $(cat $out/o/modules.txt) > $out/survey.log 2>&1
  print "survey: $(cut -f2 $out/survey.tsv 2>/dev/null | sort | uniq -c | tr '\n' ' ')"
fi
t0=$SECONDS
(cd $out && GHC="$GHCD/bin/ghc -i$src/src -i$out/stub -i$prelude -XHaskell2010 -fobject-code -outputdir $out/obj" \
  nice $law --package l $(sed "s#^$out/##" o/modules.txt) > l.log 2>&1)
print "law: rc $? $((SECONDS - t0))s"
cut -f1,2 $out/l/ledger.tsv | awk -F'\t' '{split($1, a, "/"); m = a[length(a)]; sub(/\.sexp$/, "", m); c[m "\t" $2]++} END {for (k in c) print c[k] "\t" k}' | sort -k2,2 -k3,3 | column -t
