#!/bin/bash
cd /home/peter/verify/conne-hi-bound
cp /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/Wall14PlateauIntegral.lean ConnesWeilRH/Dev/Wall14PlateauIntegral.lean
flock /tmp/connes-weil-rh-lake.lock bash -lc "timeout 1500 lake build ConnesWeilRH.Dev.Wall14PlateauIntegral" > /tmp/wbi.log 2>&1
echo "exit $?"
grep -nE "error|unsolved|type mismatch|Build completed successfully|Build completed" /tmp/wbi.log | head -20
