#!/bin/bash
# Record 1224 sec.3f: lambda=0.5 row completion (two dials; MODEL, law 65).
# Protocol identical to sec.3a/3d (see 1224_stage_a_*.md sec.3f).
# Acceptance is by LOG CONTENT, not exit code.
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1224_sweep_logs
UV=/home/peter/.local/bin/uv
mkdir -p "$LOGDIR"

run_dial() {
  local L="$1" S="$2" TAG="$3"
  echo "=== dial $TAG lambda=$L S=$S start $(date -Is)" >> "$LOGDIR/sweep3f.log"
  PROBE_LAMBDA="$L" PROBE_S="$S" PROBE_OUT="1224_dial_$TAG.json" \
    "$UV" run --with numpy --with scipy --with mpmath \
    python "$PROOF/1212_projection_trace_probe.py" \
    > "$LOGDIR/dial_$TAG.log" 2>&1
  echo "=== dial $TAG exit $? end $(date -Is)" >> "$LOGDIR/sweep3f.log"
}

run_dial 0.5 2             L05_S2
run_dial 0.5 2,3,5,7,11,13 L05_S23571113

echo "SWEEP3F COMPLETE $(date -Is)" >> "$LOGDIR/sweep3f.log"
