#!/usr/bin/env bash
set -o pipefail
D=/home/peter/projects/Connes-Weil-RH-Proof
W=/mnt/c/Projects/Connes-Weil-RH-Proof
LOG=$HOME/verify/build_crux.log
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

# sanity: my module + its new dep must exist in the ext4 copy now
for m in \
  ConnesWeilRH/Dev/C1Stage3FrontierCrux.lean \
  ConnesWeilRH/Dev/C1Stage3RemainderFamily.lean ; do
  if [ -f "$D/$m" ]; then echo "  present: $m"; else echo "  MISSING: $m"; fi
done

echo "### building C1Stage3FrontierCrux (incremental) ###"
cd "$D" || exit 1
PATH="$HOME/.elan/bin:$PATH" lake build ConnesWeilRH.Dev.C1Stage3FrontierCrux >"$LOG" 2>&1
rc=$?
echo "### lake build exit code: $rc ###"
tail -n 40 "$LOG"
