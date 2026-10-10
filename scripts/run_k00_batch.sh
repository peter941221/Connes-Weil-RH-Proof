#!/usr/bin/env bash
# K00 batch runner — executed INSIDE WSL (no $-substitution through wsl.exe).
# Rerun of the failed k00_batch: the original one-liner lost its $(cat ...)
# expansion through the Git Bash -> wsl.exe quoting gauntlet, so lake ran
# with zero targets and silently rebuilt only stale Source modules.
# xargs -a passes the 541 module names + the probe in ONE argv, no shell
# substitution involved.
set -u
cd /home/peter/projects/Connes-Weil-RH-Proof

# sync the freshly generated probe from the Windows working copy
cp /mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev/ZProbe2628K00.lean \
   ConnesWeilRH/Dev/ZProbe2628K00.lean
sed -i 's/\r$//' ConnesWeilRH/Dev/ZProbe2628K00.lean

mkdir -p /home/peter/batch2628
ls ConnesWeilRH/Dev \
  | grep '^C1RouteA.*K00.*\.lean$\|^ZProbe2628K00\.lean$' \
  | sed 's/\.lean$//' \
  | sed 's/^/ConnesWeilRH.Dev./' \
  | tr '\n' ' ' > /home/peter/batch2628/k00_targets2.txt
echo "TARGET_WORDS=$(wc -w < /home/peter/batch2628/k00_targets2.txt)"

START=$(date +%s)
xargs -a /home/peter/batch2628/k00_targets2.txt lake build \
  > /home/peter/batch2628/k00_batch2.log 2>&1
RC=$?
END=$(date +%s)
echo "LAKE_RC=$RC WALL=$((END-START))s"

O=$(ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -c 'K00.*\.olean')
echo "K00_OLEANS=$O"
P=$(ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -c 'ZProbe2628K00.olean')
echo "PROBE_OLEAN=$P"
E=$(tr -d '\0' < /home/peter/batch2628/k00_batch2.log | grep -c 'error' || true)
echo "ERROR_LINES=$E"
S=$(tr -d '\0' < /home/peter/batch2628/k00_batch2.log | grep -c 'uses sorry' || true)
echo "SORRY_LINES=$S"
tail -2 /home/peter/batch2628/k00_batch2.log
