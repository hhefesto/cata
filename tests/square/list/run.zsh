#!/usr/bin/env zsh
# tests/square/list/run.zsh LAWOUT WORK: the list pairing through the
# general checker (tests/adjoint/run.zsh).  LAWOUT: a law run's OUT on
# hs1003's exports (tests/back/run.zsh's WORK/l), which holds 00038.bend
# and HsPrelude.bend; they are staged as WORK/law/ChapterExercises.bend
# and HsPrelude.bend (a path's names may not start with a digit).  BEND,
# LEAN as tests/adjoint/run.zsh takes them.
set -u
here=${0:A:h}
lawout=${1:A} work=${2:A}
mkdir -p $work/law
cp $lawout/00038.bend $work/law/ChapterExercises.bend
cp $lawout/HsPrelude.bend $work/law/
exec $here/../../adjoint/run.zsh $here $work/law ChapterExercises.bend $work/check w=$here/w
