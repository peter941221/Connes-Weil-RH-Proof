#!/bin/bash
# Record 1342 OFFICIAL runner: m=24, NQ=2^17, resolution doubling 2^18 for
# G4; one grid, one verdict, no ladder (prereg).  Acceptance by LOG
# CONTENT (DONE 1342 sentinel + verdict line), not exit code.
# Attempt-1 (batch 1544, ABORTED-UNINFORMATIVE on the G8w rig gate) log and
# JSON are preserved verbatim as 1544_1342_official_attempt1.log and
# 1342_falsifier_results_attempt1.json (prereg 5a).  This script now runs
# attempt-2 (batch 1545, inv12 self-calibrating ladder; prereg 6b): after
# attempt-2 the probe is spent regardless of outcome.
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1342_logs
mkdir -p "$LOGDIR"
cd "$PROOF" || exit 1
PYTHONUNBUFFERED=1 P_OUT=1342_falsifier_results.json \
  /home/peter/.local/bin/uv run --no-project \
  --with numpy --with scipy --with mpmath \
  python "$PROOF/1342_prime_free_falsifier_probe.py" \
  > "$LOGDIR/1545_1342_official_attempt2.log" 2>&1
echo "official exit $?"
