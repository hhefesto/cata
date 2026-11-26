#!/usr/bin/env zsh
# run-prelude.zsh PKG OUT: a fold or law package's modules as they are to run:
# without their laws (the .exK defs), HsPrelude's Map and Set the balanced trees
# of prelude/run/HsMapTree.bend and its Int the integers past 2^48 of
# prelude/run/HsIntBig.bend (the same headers; the lists and the Nats are what
# the laws are told on). The tree file's parts go after the prelude's defs they name
# (#@after NAME). RUN_PARTS: the run files to use (all of prelude/run).
set -eu
here=${0:A:h}/..
pkg=$1 out=$2
parts=(${=RUN_PARTS:-})
(( $#parts )) || parts=($here/prelude/run/*.bend)
mkdir -p $out
awk '
  function name(l) { sub(/^(def|type) /, "", l); sub(/[(<: ].*/, "", l); return l }
  FNR == NR {
    if ($0 ~ /^#@after /) { sect = $2; next }
    if ($0 ~ /^#@drop /) { t[$2] = 1; next }
    if ($0 ~ /^(def|type) /) t[name($0)] = 1
    part[sect] = part[sect] $0 "\n"; next
  }
  /^(def|type) / {
    if (last in part) { printf "%s\n", part[last]; delete part[last] }
    last = name($0); drop = (last in t)
  }
  { if (!drop) print }
' <(cat $parts) $pkg/HsPrelude.bend > $out/HsPrelude.bend
for f in $pkg/*.bend; do
  n=${f:t}
  case $n in HsPrelude.bend|*_all.bend|*_try.bend|Why_*|X1.bend|Dx.bend) continue ;; esac
  awk '/^(def|type|law|import) /{ p = ($0 !~ /^(def|law) [A-Za-z0-9_.]*\.ex[0-9]+\(/) } /^#/ { next } p || NR == 1' $f > $out/$n
done
