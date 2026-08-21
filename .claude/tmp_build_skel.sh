#!/usr/bin/env bash
set -o pipefail
D=/home/peter/projects/Connes-Weil-RH-Proof
W=/mnt/c/Projects/Connes-Weil-RH-Proof
LOG=$HOME/verify/build_skel.log
mkdir -p "$HOME/verify"

echo "### mirroring ALL .lean sources from Windows (source of truth) into ext4 copy ###"
cd "$W/ConnesWeilRH" || exit 1
n=0
while IFS= read -r f; do
  rel="${f#./}"
  mkdir -p "$D/ConnesWeilRH/$(dirname "$rel")"
  cp "$W/ConnesWeilRH/$rel" "$D/ConnesWeilRH/$rel" || { echo "COPY FAILED: $rel"; exit 1; }
  n=$((n+1))
done < <(find . -name '*.lean' -type f)
echo "### mirrored $n lean files ###"

echo "### building ConnesWeilRH.Dev.UnconditionalSkeleton (incremental) ###"
cd "$D" || exit 1
PATH="$HOME/.elan/bin:$PATH" lake build ConnesWeilRH.Dev.UnconditionalSkeleton >"$LOG" 2>&1
rc=$?
echo "### lake build exit code: $rc ###"
tail -n 50 "$LOG"
