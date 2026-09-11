#!/bin/bash
# Record 1342 SMOKE runner (P_SMOKE=1): machinery only, band NOT
# adjudicated; digits non-representative (prereg smoke policy).
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1342_logs
mkdir -p "$LOGDIR"
cd "$PROOF" || exit 1
PYTHONUNBUFFERED=1 P_SMOKE=1 /home/peter/.local/bin/uv run --no-project \
  --with numpy --with scipy --with mpmath \
  python "$PROOF/1342_prime_free_falsifier_probe.py" \
  > "$LOGDIR/1342_smoke1.log" 2>&1
echo "smoke exit $?"
