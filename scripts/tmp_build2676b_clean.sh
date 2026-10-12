#!/bin/bash
# 2676 module-1 rebuild (module 1 only; upstream three already built).
# Logs WSL-side first, then copies out (log-not-pipe).
set -u
WIN=/mnt/c/Projects/Connes-Weil-RH-Proof
LOG=/home/peter/rh/build-logs/2676_module1b.log
mkdir -p /home/peter/rh/build-logs
cd /home/peter/rh || exit 1
cp "$WIN/ConnesWeilRH/Dev/C1RouteACellContainment2676.lean" ConnesWeilRH/Dev/C1RouteACellContainment2676.lean || exit 1
a=$(md5sum "$WIN/ConnesWeilRH/Dev/C1RouteACellContainment2676.lean" | cut -d' ' -f1)
b=$(md5sum ConnesWeilRH/Dev/C1RouteACellContainment2676.lean | cut -d' ' -f1)
{
  if [ "$a" = "$b" ]; then echo "sync OK $a"; else echo "sync MISMATCH"; exit 1; fi
  PKGPATHS=$(find .lake/packages -type d -path "*/build/lib/lean" | paste -sd:)
  export LEAN_PATH="/home/peter/rh/.lake/build/lib/lean:$PKGPATHS"
  /home/peter/.elan/bin/lean -o .lake/build/lib/lean/ConnesWeilRH/Dev/C1RouteACellContainment2676.olean ConnesWeilRH/Dev/C1RouteACellContainment2676.lean
  echo "LEAN_EXIT=$?"
} > "$LOG" 2>&1
cp "$LOG" "$WIN/build-logs/2676_module1b.log"
echo "--- tail of log:"
tail -40 "$LOG"
