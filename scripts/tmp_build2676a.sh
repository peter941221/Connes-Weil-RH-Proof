#!/bin/bash
# 2676 module-1 smoke build: sync 4 files, rebuild in dependency order with
# direct lean + explicit LEAN_PATH (lake env hangs on this mirror).
set -u
WIN=/mnt/c/Projects/Connes-Weil-RH-Proof
cd /home/peter/rh || exit 1
for f in C1RouteAIntervalAlgebra C1RouteABinary64Bridge2674 C1RouteACellIntegralCharge2675 C1RouteACellContainment2676; do
  cp "$WIN/ConnesWeilRH/Dev/$f.lean" "ConnesWeilRH/Dev/$f.lean" || exit 1
done
echo "synced; md5 cross-check:"
for f in C1RouteAIntervalAlgebra C1RouteABinary64Bridge2674 C1RouteACellIntegralCharge2675 C1RouteACellContainment2676; do
  a=$(md5sum "$WIN/ConnesWeilRH/Dev/$f.lean" | cut -d' ' -f1)
  b=$(md5sum "ConnesWeilRH/Dev/$f.lean" | cut -d' ' -f1)
  if [ "$a" = "$b" ]; then echo "$f OK"; else echo "$f MISMATCH"; exit 1; fi
done
PKGPATHS=$(find .lake/packages -type d -path "*/build/lib/lean" | paste -sd:)
export LEAN_PATH="/home/peter/rh/.lake/build/lib/lean:$PKGPATHS"
LEAN=/home/peter/.elan/bin/lean
OUT=.lake/build/lib/lean/ConnesWeilRH/Dev
mkdir -p "$OUT"
for f in C1RouteAIntervalAlgebra C1RouteABinary64Bridge2674 C1RouteACellIntegralCharge2675 C1RouteACellContainment2676; do
  echo "=== building $f"
  if "$LEAN" -o "$OUT/$f.olean" "ConnesWeilRH/Dev/$f.lean" 2>&1; then
    echo "=== $f DONE"
  else
    echo "=== $f FAILED (exit above)"
    break
  fi
done
echo "=== all stages attempted"
