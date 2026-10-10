#!/usr/bin/env bash
# Sync the missing owner-0 edge module into the WSL mirror, verify bytes,
# then rebuild the probe alone with triple acceptance.
set -u
cd /home/peter/projects/Connes-Weil-RH-Proof

cp /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/C1RouteAMomentActualEdge2620.lean \
   ConnesWeilRH/Dev/C1RouteAMomentActualEdge2620.lean
sed -i 's/\r$//' ConnesWeilRH/Dev/C1RouteAMomentActualEdge2620.lean

echo "WIN_SHA=$(sha256sum /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/C1RouteAMomentActualEdge2620.lean | cut -c1-16)"
echo "WSL_SHA=$(sha256sum ConnesWeilRH/Dev/C1RouteAMomentActualEdge2620.lean | cut -c1-16)"

START=$(date +%s)
lake build ConnesWeilRH.Dev.ZProbe2628K00 > /home/peter/batch2628/k00_probe.log 2>&1
RC=$?
END=$(date +%s)
echo "LAKE_RC=$RC WALL=$((END-START))s"

P=$(ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -c 'ZProbe2628K00\.olean')
echo "PROBE_OLEAN=$P"
E=$(tr -d '\0' < /home/peter/batch2628/k00_probe.log | grep -c 'error' || true)
echo "ERROR_LINES=$E"
S=$(tr -d '\0' < /home/peter/batch2628/k00_probe.log | grep -c 'uses sorry' || true)
echo "SORRY_LINES=$S"
T=$(grep -c '^theorem\|^private theorem' ConnesWeilRH/Dev/ZProbe2628K00.lean)
echo "THEOREMS=$T"
tail -2 /home/peter/batch2628/k00_probe.log
