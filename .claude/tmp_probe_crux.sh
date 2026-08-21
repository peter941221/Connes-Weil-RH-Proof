#!/usr/bin/env bash
set -o pipefail
D=/home/peter/projects/Connes-Weil-RH-Proof
cd "$D" || exit 1

PROBE=ConnesWeilRH/Dev/CruxAxiomProbe.lean
cat > "$PROBE" <<'LEAN'
import ConnesWeilRH.Dev.C1Stage3FrontierCrux

#check ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_closes_healthyCriterionState

#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_detectorTrace_eq_qw
#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_reTrace_eq_hilbertSchmidtMass
#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_closes_healthyCriterionState
LEAN

echo "=== #check: closure theorem type ==="
PATH="$HOME/.elan/bin:$PATH" lake env lean "$PROBE" 2>&1 | grep -vi "^warning\|^note:\|exceeds the 100\|linter.unusedVariables\|unused variable\|try 'simp'\|linter.unnecessarySimpa\|automatically included\|consider restructuring\|omit \["
echo "=== probe done (rc=$?) ==="
rm -f "$PROBE"
