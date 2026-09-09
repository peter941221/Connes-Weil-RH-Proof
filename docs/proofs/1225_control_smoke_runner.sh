#!/bin/bash
# Record 1225: SMOKE pass of the positive-control probe (diagnostic only,
# never an official readout).  Acceptance is by LOG CONTENT, not exit code.
set -u
PROOF=/home/peter/rh/docs/proofs
UV=/home/peter/.local/bin/uv
PROBE_SMOKE=1 "$UV" run --with numpy --with scipy --with mpmath \
  python "$PROOF/1225_positive_control_probe.py" \
  > "$PROOF/1225_smoke1.log" 2>&1
echo "smoke exit $?"
