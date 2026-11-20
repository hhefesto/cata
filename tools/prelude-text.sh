#!/usr/bin/env zsh
# Writes bend/Prelude.bend from prelude/*.bend: each file's text as defs
# that answer it (Bend's compiler takes no string literal much longer than
# 4 KB, so in pieces), which the fold writes into HsPrelude.bend
# (bend/Fold.bend, fd.hsprelude.write). prelude/NAME.bend is
# `pre.NAME()`. Run it after editing a file there; a fold run then checks
# the prelude with the modules (`bend --check-only`).
set -eu
cd ${0:A:h}/..
{
  print -r -- "# Written by tools/prelude-text.sh from prelude/*.bend: edit those, then run it."
  print -r -- "import Base"
  print -r -- ""
  for f in prelude/*.bend; do
    awk -v name="${f:t:r}" '
      function flush() {
        printf "def pre.%s.p%d() -> String:\n  \"%s\"\n\n", name, k, chunk
        k++
        chunk = ""
      }
      BEGIN { k = 0; chunk = "" }
      {
        line = $0
        gsub(/\\/, "\\\\", line)
        gsub(/"/, "\\\"", line)
        if (chunk != "" && length(chunk) + length(line) > 2800) flush()
        chunk = chunk line "\\n"
      }
      END {
        if (chunk != "") flush()
        printf "def pre.%s() -> String:\n  ", name
        for (i = 0; i < k; i++) printf "%spre.%s.p%d()", (i ? " ++ " : ""), name, i
        printf "\n"
      }' $f
  done
} > bend/Prelude.bend
