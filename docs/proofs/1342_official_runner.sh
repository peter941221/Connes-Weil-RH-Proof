#!/bin/bash
# Record 1342 OFFICIAL runner: m=24, NQ=2^17, resolution doubling 2^18 for
# G4; one grid, one verdict, no ladder (prereg).  Acceptance by LOG
# CONTENT (DONE 1342 sentinel + verdict line), not exit code.
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1342_logs
mkdir -p "$LOGDIR"
cd "$PROOF" || exit 1
PYTHONUNBUFFERED=1 P_OUT=1342_falsifier_results.json \
  /home/peter/.local/bin/uv run --no-project \
  --with numpy --with scipy --with mpmath \
  python "$PROOF/1342_prime_free_falsifier_probe.py" \
  > "$LOGDIR/1544_1342_official.log" 2>&1
echo "official exit $?"
