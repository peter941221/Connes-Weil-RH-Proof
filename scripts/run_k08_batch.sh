#!/usr/bin/env bash
# K08 batch runner — executed INSIDE WSL (no $-substitution through wsl.exe).
# Copies the freshly generated owner-02 stack (541 family modules + edge
# pair + ZProbe2628K08), builds all 544 targets via xargs -a (AGENTS 2cd
# law: target lists go by file, never $(cat ...) through wsl.exe), then
# triple file-level acceptance (olean census, full error list, uses sorry).
set -u
cd /home/peter/projects/Connes-Weil-RH-Proof

W=/mnt/c/Projects/Connes-Weil-RH-Proof/ConnesWeilRH/Dev
COPIED=0
for f in $(ls "$W" | grep 'K08'); do
  cp "$W/$f" "ConnesWeilRH/Dev/$f"
  sed -i 's/\r$//' "ConnesWeilRH/Dev/$f"
  COPIED=$((COPIED+1))
done
echo "COPIED=$COPIED"

mkdir -p /home/peter/batch2628
ls ConnesWeilRH/Dev \
  | grep '^C1RouteA.*K08.*\.lean$\|^ZProbe2628K08\.lean$' \
  | sed 's/\.lean$//' \
  | sed 's/^/ConnesWeilRH.Dev./' \
  | tr '\n' ' ' > /home/peter/batch2628/k02_targets.txt
echo "TARGET_WORDS=$(wc -w < /home/peter/batch2628/k02_targets.txt)"

START=$(date +%s)
xargs -a /home/peter/batch2628/k02_targets.txt lake build \
  > /home/peter/batch2628/k02_batch.log 2>&1
RC=$?
END=$(date +%s)
echo "LAKE_RC=$RC WALL=$((END-START))s"

O=$(ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -c 'K08.*\.olean')
echo "K08_OLEANS=$O"
P=$(ls .lake/build/lib/lean/ConnesWeilRH/Dev/ | grep -c 'ZProbe2628K08.olean')
echo "PROBE_OLEAN=$P"
E=$(tr -d '\0' < /home/peter/batch2628/k02_batch.log | grep -c 'error' || true)
echo "ERROR_LINES=$E"
S=$(tr -d '\0' < /home/peter/batch2628/k02_batch.log | grep -c 'uses sorry' || true)
echo "SORRY_LINES=$S"
tail -2 /home/peter/batch2628/k02_batch.log
