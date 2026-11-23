#!/usr/bin/env zsh
# tree.zsh HSDIR TREE: G's modules (HSDIR/Telomare_IR_Core.hs, module
# Telomare.IR.Core) linked where GHC looks for them by name
# (TREE/Telomare/IR/Core.hs), so a module's imports of the package's
# other modules find them
set -u
hs=${1:A} tree=${2:A}
rm -rf $tree; mkdir -p $tree
for f in $hs/*.hs; do
  m=$(grep -m1 '^module ' $f | awk '{print $2}')
  [[ -n $m ]] || continue
  p=$tree/${m//.//}.hs
  mkdir -p ${p:h}; ln -sf $f $p
done
