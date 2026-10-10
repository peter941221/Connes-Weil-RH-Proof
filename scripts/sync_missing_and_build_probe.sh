#!/usr/bin/env bash
# Sync every probe-closure module missing from the WSL mirror, then
# rebuild ZProbe2628K00 with triple file-level acceptance.
set -u
cd /home/peter/projects/Connes-Weil-RH-Proof

SYNCED=0
while read -r m; do
  f="ConnesWeilRH/Dev/$m.lean"
  if [ ! -f "$f" ]; then
    cp "/mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/$m.lean" "$f"
    sed -i 's/\r$//' "$f"
    echo "SYNCED $m"
    SYNCED=$((SYNCED+1))
  fi
done < /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/_k00_closure.txt
echo "SYNCED_COUNT=$SYNCED"

START=$(date +%s)
lake build ConnesWeilRH.Dev.ZProbe2628K00 > /home/peter/batch2628/k00_probe2.log 2>&1
RC=$?
END=$(date +%s)
echo "LAKE_RC=$RC WALL=$((END-START))s"

P=$(ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -c 'ZProbe2628K00\.olean')
echo "PROBE_OLEAN=$P"
E=$(tr -d '\0' < /home/peter/batch2628/k00_probe2.log | grep -c 'error' || true)
echo "ERROR_LINES=$E"
S=$(tr -d '\0' < /home/peter/batch2628/k00_probe2.log | grep -c 'uses sorry' || true)
echo "SORRY_LINES=$S"
tail -2 /home/peter/batch2628/k00_probe2.log
