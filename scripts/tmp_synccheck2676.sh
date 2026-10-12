#!/bin/bash
# 2676 pre-build: check mirror branch state and md5 of the three upstream modules.
cd /home/peter/rh || exit 1
echo "BRANCH=$(git branch --show-current)"
for f in C1RouteAIntervalAlgebra C1RouteABinary64Bridge2674 C1RouteACellIntegralCharge2675 C1RouteACellContainment2676; do
  w="/mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/$f.lean"
  l="ConnesWeilRH/Dev/$f.lean"
  wm=$(md5sum "$w" 2>/dev/null | cut -d' ' -f1)
  lm=$(md5sum "$l" 2>/dev/null | cut -d' ' -f1)
  if [ "$wm" = "$lm" ]; then st=SAME; else st=DIFF; fi
  echo "$f win=$wm wsl=$lm $st"
done
ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -E "IntervalAlgebra|Binary64Bridge2674|CellIntegralCharge2675|CellContainment2676" || echo "NO_OLEANS"
