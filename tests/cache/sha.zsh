#!/usr/bin/env zsh
# tests/cache/sha.zsh [FILE...]: bend/Cache.bend's SHA-256 against
# sha256sum on files of the sizes SHA-256's padding turns on (0, 1, 55, 56,
# 63, 64, 65, 119, 120 bytes) and on any FILE given, then each file's entry
# put and read back whole, and read back as none once cut short. BEND
# names the bend. Prints PASS or FAIL.
set -u
here=${0:A:h}
bend=${BEND:-bend}
w=$(mktemp -d /tmp/ct-sha.XXXXXX)
for n in 0 1 55 56 63 64 65 119 120 1000; do
  head -c $n /dev/urandom > $w/r$n
done
files=($w/r* "$@")
(cd $here && BEND_NO_TELEMETRY=1 $bend Sha.bend -o $w/sha > $w/build.log 2>&1) || { cat $w/build.log; print FAIL build; exit 1 }
mkdir -p $w/cache
CACHE_TEST=$w/cache $w/sha $files > $w/got
grep -v '^round ' $w/got > $w/ours
sha256sum $files > $w/theirs
fail=0
if cmp -s $w/ours $w/theirs; then print "sha256: ${#files} files the same as sha256sum"; else diff $w/ours $w/theirs; fail=1; fi
nr=$(grep -c '^round same cut none ' $w/got)
if (( nr == ${#files} )); then print "entries: $nr read back whole, none once cut"; else grep '^round' $w/got; fail=1; fi
rm -r $w
(( fail == 0 )) && print PASS || print FAIL
exit $fail
