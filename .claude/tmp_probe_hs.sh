#!/usr/bin/env bash
set -o pipefail
D=/home/peter/projects/Connes-Weil-RH-Proof
W=/mnt/c/Projects/Connes-Weil-RH-Proof
OUT="$W/.claude/probe_hs_out.txt"
cd "$D" || exit 1

PROBE=ConnesWeilRH/Dev/HsAxiomProbe.lean
cat > "$PROBE" <<'LEAN'
import ConnesWeilRH.Dev.C1Stage3FrontierHS

#print axioms ConnesWeilRH.Source.C1Stage3FrontierHS.frontierBareSectionEnergy_eq_massTimesMeasure
#print axioms ConnesWeilRH.Source.C1Stage3FrontierHS.frontierBareHS_windowEnergy_unbounded
LEAN

PATH="$HOME/.elan/bin:$PATH" lake env lean "$PROBE" >"$OUT" 2>&1
echo "exit=$?" | tee -a "$OUT"
rm -f "$PROBE"
echo "wrote $OUT"
