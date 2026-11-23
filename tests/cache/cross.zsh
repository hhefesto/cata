#!/usr/bin/env zsh
# tests/cache/cross.zsh OLD NEW WORK -- LAW-ARGS...: law's cache across a
# change of cata's rules.  OLD and NEW are two law binaries (two versions
# of the rules).  OLD runs with an empty cache (WORK/o, filling
# WORK/cache); NEW runs with that cache (WORK/n) and with none (WORK/u).
# NEW's outputs must be the same with the old cache as without it (a file
# OLD wrote differently is checked again, a file it wrote the same is an
# answer kept), and the calls NEW made with the cache are what the rules'
# change cost.  LAW-ARGS as tests/cache/run.zsh's; BEND and GHC too.
# The files OLD and NEW wrote differently are named: when bend made no call
# with the cache although some differ, they must be files no check reads
# (a ledger, a drops list), never a .bend file bend checked.
set -u
old=${1:A} new=${2:A} work=${3:A}
shift 3
[[ $1 == -- ]] && shift
pkg=()
if [[ $1 == --package ]]; then pkg=(--package); shift; fi
shift   # OUT, replaced
files=("$@")
mkdir -p $work/bin
rm -rf $work/o $work/n $work/u $work/cache $work/*.calls*(N)
real_bend=${BEND:-bend}
ghc_words=(${=GHC:-ghc})
for t in bend ghc; do
  print -r -- '#!/usr/bin/env zsh
print -r -- "$*" >> $CALLS.'$t'
exec $REAL_'${(U)t}' "$@"' > $work/bin/$t
  chmod +x $work/bin/$t
done
export REAL_BEND=$real_bend REAL_GHC=$ghc_words[1]
export BEND=$work/bin/bend GHC="$work/bin/ghc ${(j: :)ghc_words[2,-1]}"
run() {
  local name=$1 law=$2; shift 2
  local t0=$SECONDS
  mkdir -p $work/$name
  CALLS=$work/$name.calls "$@" nice -n 10 $law $pkg $work/$name $files > $work/$name.log 2>&1
  local rc=$?
  local nb=$( [[ -f $work/$name.calls.bend ]] && wc -l < $work/$name.calls.bend || print 0)
  local ng=$( [[ -f $work/$name.calls.ghc ]] && wc -l < $work/$name.calls.ghc || print 0)
  print "$name: rc $rc, $((SECONDS - t0)) s, bend $nb calls, ghc $ng calls"
}
run o $old env CATA_CACHE=$work/cache
print "cache after OLD: $(ls $work/cache | wc -l) entries"
run n $new env CATA_CACHE=$work/cache
run u $new env -u CATA_CACHE
nf=$(cd $work/u && find . -type f | wc -l)
n=0
for f in $(cd $work/u && find . -type f); do
  cmp -s $work/u/$f $work/n/$f || { (( n < 5 )) && print "differs: n/$f"; n=$((n + 1)) }
done
d=0
for f in $(cd $work/u && find . -type f); do
  cmp -s $work/u/$f $work/o/$f || { (( d < 5 )) && print "rules changed: $f"; d=$((d + 1)) }
done
print "OLD vs NEW (no cache): $d of $nf files differ (what the rules changed)"
print "NEW with OLD's cache vs NEW without: $nf files, $n differ"
if (( nf > 0 && n == 0 )) && diff <(cd $work/u && find . -type f | sort) <(cd $work/n && find . -type f | sort) > /dev/null; then
  print SAME; exit 0
fi
print DIFFERENT; exit 1
