#!/usr/bin/env bash
set -o pipefail
D=/home/peter/projects/Connes-Weil-RH-Proof
W=/mnt/c/Projects/Connes-Weil-RH-Proof
OUT="$W/.claude/probe_skel_out.txt"

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

cd "$D" || exit 1
: >"$OUT"
echo "=== #check / #print / #print axioms : unconditional_rh_skeleton (Route A) + Stage-3 frontiers (Route B) ===" >>"$OUT"
PATH="$HOME/.elan/bin:$PATH" lake env lean ConnesWeilRH/Dev/UnifiedRemainingGapsRouteAudit.lean >"$OUT.body" 2>&1
rc=$?
cat "$OUT.body" >>"$OUT"
echo "exit=$rc" | tee -a "$OUT"
rm -f "$OUT.body"
echo "wrote $OUT"
