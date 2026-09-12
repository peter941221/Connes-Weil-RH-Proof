#!/bin/bash
# Record 1348 A1b OFFICIAL runner (batch 1548).
# Deep ladder m in {192, 384} on the G9-certified fast path; G10
# cross-run reproduction at m=96; branch bands locked in
# 1348_a1b_deep_ladder_prg.md BEFORE launch (law 42); the 384 rung is
# guarded by the CLOCK-ONLY budget kill (2.5 h) and 8 h hard stop.
# Fidelity pins: numpy==2.5.3 / mpmath==1.4.1 (A1 reproduction context).
# Acceptance is by LOG CONTENT ("DONE 1348-A1B" sentinel), not exit code.
set -u
PROOF=/home/peter/rh/docs/proofs
LOG=$PROOF/1548_1348_a1b_official.log
cd "$PROOF" || exit 1
PYTHONUNBUFFERED=1 P_OUT=1348_a1b_results.json \
  /home/peter/.local/bin/uv run --no-project \
  --with numpy==2.5.3 --with scipy --with mpmath==1.4.1 \
  python "$PROOF/1348_a1b_deep_ladder_probe.py" > "$LOG" 2>&1
echo "official exit $?"
tail -n 16 "$LOG"
echo RUNNER_DONE
