#!/bin/bash
# Record 1354 log-slack rung-II OFFICIAL runner (batch 1549).
# Full-dump re-run m in {192, 384} on the G9-certified fast path; R
# cross-run reproduction vs committed 1348 digits (rel < 5e-13); bands
# locked in 1354_logslack_extension_prg.md BEFORE launch (law 42);
# CLOCK-ONLY 4 h hard stop at rung entry.
# Fidelity pins: numpy==2.5.3 / mpmath==1.4.1 (A1/A1b context).
# Acceptance is by LOG CONTENT ("DONE 1354-RUNG2" sentinel), not exit
# code.
set -u
PROOF=/home/peter/rh/docs/proofs
LOG=$PROOF/1549_1354_rung2_official.log
cd "$PROOF" || exit 1
PYTHONUNBUFFERED=1 P_OUT=1354_rung2_results.json \
  /home/peter/.local/bin/uv run --no-project \
  --with numpy==2.5.3 --with scipy --with mpmath==1.4.1 \
  python "$PROOF/1354_rung2_logslack_probe.py" > "$LOG" 2>&1
echo "official exit $?"
tail -n 16 "$LOG"
echo RUNNER_DONE
