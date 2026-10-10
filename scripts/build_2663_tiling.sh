#!/bin/bash
# Record-2663: sync the hand tiling module into the WSL mirror and compile it
# with a direct `lean` call (lake env hangs on this mirror; direct lean with an
# explicit LEAN_PATH is the house path). All verdicts go to the log file.
cd /home/peter/rh || exit 1
cp /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean \
   ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean
echo "=== md5 (mirror, windows) ==="
md5sum ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean \
       /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean
PKGPATHS=$(find .lake/packages -type d -path "*/build/lib/lean" | paste -sd:)
export LEAN_PATH="$PWD/.lake/build/lib/lean:$PKGPATHS"
LOG=/mnt/c/Projects/Connes-Weil-RH-Proof/results/build_2663_tiling.log
T0=$(date +%s)
/home/peter/.elan/bin/lean -o ConnesWeilRH/Dev/C1RouteAEntryTiling2663.olean \
  ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean > "$LOG" 2>&1
EXIT=$?
T1=$(date +%s)
{
  echo "=== summary ==="
  echo "LEAN_EXIT=$EXIT"
  echo "WALL_SECONDS=$((T1 - T0))"
  ls -la ConnesWeilRH/Dev/C1RouteAEntryTiling2663.olean 2>&1
  echo "ERRCOUNT=$(grep -c '^error' "$LOG")"
  echo "SORRYCOUNT=$(grep -c 'uses sorry' "$LOG")"
  echo "AXIOM_RECORDS=$(grep -c 'depends on axioms' "$LOG")"
  echo "AXIOM_TRIO=$(grep -c 'propext, Classical.choice, Quot.sound' "$LOG")"
  echo "SUCCESS_LINE=$(grep -c 'Build completed successfully' "$LOG")"
} >> "$LOG" 2>&1
echo "done"