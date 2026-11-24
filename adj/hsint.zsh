#!/usr/bin/env zsh
# adj/hsint.zsh: the prelude's own HsInt is the model's Int.  Writes
# HsInt.bend (the prelude's HsInt, the text Fold.bend writes into
# HsPrelude.bend, and prelude/HsPartial.bend's division by a HsInt that may
# be 0) and checks HSINT.bend, which proves HsInt.add, sub, is_lt and
# HsNum.idiv, imod to be Core.bend's z.add, z.sub, z.lt, z.div and z.mod at
# every pair, --check-only then --verdict.
#   BEND the bend; LEAN a directory holding Lean 4.34.0's lean (for
#   --verdict); HSPRELUDE a HsPrelude.bend cata wrote, whose HsInt must be
#   this one.  Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
[[ -n ${LEAN:-} ]] && export PATH=$LEAN:$PATH
cd $here
ints=$(awk '/^def fd\.hsprelude\.i[12]\(\) -> String:/ {on = 1; next}
  on {s = $0; sub(/^  "/, "", s); sub(/"$/, "", s); gsub(/\\n/, "\n", s); gsub(/\\"/, "\"", s); gsub(/\\\\/, "\\", s); printf "%s", s; on = 0}' ../bend/Fold.bend)
part=$(awk '/^def HsNum\.i(div|mod|quot|rem)\(/ {on = 1} /^$/ {if (on) print ""; on = 0} on {print}' ../prelude/HsPartial.bend)
{
  print -r -- "# Written by adj/hsint.zsh from bend/Fold.bend and prelude/HsPartial.bend."
  print -r -- "import Base"
  print -r -- ""
  print -r -- "$ints"
  print -r -- ""
  print -r -- "$part"
} > HsInt.bend
ok=1
if [[ -n ${HSPRELUDE:-} ]]; then
  # every line of HsInt.bend's HsInt, in order, in what cata wrote
  a=$(awk '/^type HsInt is Data/ {on = 1} on' HsInt.bend | awk '/^def HsInt\.(of|neg|negate|nsub|add|sub|mul|cmp|is_|mag|isneg|quot|rem|div|mod)/ {on = 1} /^$/ {on = 0} on')
  b=$(awk '/^type HsInt is Data/ {on = 1} on' $HSPRELUDE | awk '/^def HsInt\.(of|neg|negate|nsub|add|sub|mul|cmp|is_|mag|isneg|quot|rem|div|mod)/ {on = 1} /^$/ {on = 0} on')
  if [[ -n $a && $a == $b ]]; then print "HsPrelude's HsInt: the same"; else print "HsPrelude's HsInt: differs"; ok=0; fi
fi
c=$(BEND_NO_TELEMETRY=1 $bend HSINT.bend --check-only 2>&1)
print -r -- "HSINT check: ${c//$'\n'/ | }"
v=$(BEND_NO_TELEMETRY=1 $bend HSINT.bend --verdict 2>&1)
print -r -- "HSINT verdict: ${v//$'\n'/ | }"
[[ $c == "ALL PROOFS CHECK"* && $v == "ALL PROOFS CHECK"* ]] || ok=0
if (( ok )); then print PASS; else print FAIL; exit 1; fi
