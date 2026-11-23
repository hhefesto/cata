#!/usr/bin/env zsh
# tests/cache/run.zsh LAW WORK -- LAW-ARGS...: whether law's cache
# (CATA_CACHE, bend/Cache.bend) changes nothing.  Runs LAW three times on
# LAW-ARGS (`--package OUT FILES...` or `OUT FILES...`, OUT replaced): with
# no cache (WORK/u), with an empty cache (WORK/c, which fills WORK/cache)
# and with that cache (WORK/w); counts each run's calls of bend and GHC
# (through counting shims in WORK/bin); and compares every file the three
# runs wrote, byte for byte.  BEND names the bend; GHC the ghc and its
# flags (as law takes them).  Prints each run's seconds and calls, then
# SAME or DIFFERENT, and exits 1 when any file differs.
set -u
law=${1:A} work=${2:A}
shift 2
[[ $1 == -- ]] && shift
pkg=()
if [[ $1 == --package ]]; then pkg=(--package); shift; fi
shift   # OUT, replaced
files=("$@")
mkdir -p $work/bin
rm -rf $work/u $work/c $work/w $work/cache $work/*.calls*(N)
real_bend=${BEND:-bend}
ghc_words=(${=GHC:-ghc})
real_ghc=$ghc_words[1]
for t in bend ghc; do
  print -r -- '#!/usr/bin/env zsh
print -r -- "$*" >> $CALLS.'$t'
exec $REAL_'${(U)t}' "$@"' > $work/bin/$t
  chmod +x $work/bin/$t
done
export REAL_BEND=$real_bend REAL_GHC=$real_ghc
export BEND=$work/bin/bend GHC="$work/bin/ghc ${(j: :)ghc_words[2,-1]}"
run() {
  local name=$1; shift
  local t0=$SECONDS
  mkdir -p $work/$name
  CALLS=$work/$name.calls "$@" nice -n 10 $law $pkg $work/$name $files > $work/$name.log 2>&1
  local rc=$?
  local nb=$( [[ -f $work/$name.calls.bend ]] && wc -l < $work/$name.calls.bend || print 0)
  local ng=$( [[ -f $work/$name.calls.ghc ]] && wc -l < $work/$name.calls.ghc || print 0)
  print "$name: rc $rc, $((SECONDS - t0)) s, bend $nb calls, ghc $ng calls"
}
run u env -u CATA_CACHE
run c env CATA_CACHE=$work/cache
print "cache: $(ls $work/cache | wc -l) entries, $(du -sh $work/cache | cut -f1)"
run w env CATA_CACHE=$work/cache
same=1
nu=$(cd $work/u && find . -type f | wc -l)
(( nu > 0 )) || { print "u wrote nothing"; same=0 }
for a in c w; do
  if ! diff <(cd $work/u && find . -type f | sort) <(cd $work/$a && find . -type f | sort) > /dev/null; then
    print "u and $a wrote different files"; same=0
  fi
  n=0
  for f in $(cd $work/u && find . -type f); do
    cmp -s $work/u/$f $work/$a/$f || { (( n < 5 )) && print "differs: $a/$f"; n=$((n + 1)) }
  done
  print "u vs $a: $(cd $work/u && find . -type f | wc -l) files, $n differ"
  (( n == 0 )) || same=0
done
(( same )) && print SAME || print DIFFERENT
(( same ))
