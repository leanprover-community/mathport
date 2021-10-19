#!/usr/bin/env bash
# Usage: mk_all.sh [subdirectory]
#

cd $1
find . -name \*.lean -not -name all.lean \
  | sed 's,^\./,,;s,\.lean$,,;s,/,.,g;s,^,import ,' \
  | sort > ./all.lean
