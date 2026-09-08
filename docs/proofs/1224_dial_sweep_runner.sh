#!/bin/bash
# Record 1224 sec.3a: model-level dial-sensitivity sweep (MODEL, law 65).
# Five dials of the 1212 probe; the (1.0,{2,3,5}) replay is the regression
# gate against the committed 1213 numbers.  S0 gate failures abort the
# affected dial only (1097 protocol).  Acceptance is by LOG CONTENT, not
# exit code.  Run from the Linux-side verification environment; logs land
# under 1224_sweep_logs/.
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1224_sweep_logs
UV=/home/peter/.local/bin/uv
mkdir -p "$LOGDIR"

run_dial() {
  local L="$1" S="$2" TAG="$3"
  echo "=== dial $TAG lambda=$L S=$S start $(date -Is)" >> "$LOGDIR/sweep.log"
  PROBE_LAMBDA="$L" PROBE_S="$S" PROBE_OUT="1224_dial_$TAG.json" \
    "$UV" run --with numpy --with scipy --with mpmath \
    python "$PROOF/1212_projection_trace_probe.py" \
    > "$LOGDIR/dial_$TAG.log" 2>&1
  echo "=== dial $TAG exit $? end $(date -Is)" >> "$LOGDIR/sweep.log"
}

# registered grid (1224 sec.3a)
run_dial 1.0 2,3,5         L10_S235        # replay / regression gate
run_dial 0.5 2,3,5         L05_S235
run_dial 2.0 2,3,5         L20_S235
run_dial 1.0 2             L10_S2
run_dial 1.0 2,3,5,7,11,13 L10_S23571113

echo "SWEEP COMPLETE $(date -Is)" >> "$LOGDIR/sweep.log"
