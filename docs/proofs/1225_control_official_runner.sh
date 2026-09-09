#!/bin/bash
# Record 1225 section 4: OFFICIAL positive-control run (MODEL rig, law 65).
# Registered dials: lambda=1, S=2,3,5 (script defaults), CONTROL_EPS=0.03,
# ladder n in {8,16,32,64} x dt-pair (8192,16384), eps_q 1e-8, cap 16385.
# A4b rank rule: PROBE_RANK=2560 (measured Slepian-knee capture; every
# official rung must certify tail_gap < 1e-10 or the invocation aborts
# ABORTED-UNINFORMATIVE).  C4 detector-twin replay gate runs in the same
# invocation.  Acceptance is by LOG CONTENT, not exit code.
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1225_control_logs
mkdir -p "$LOGDIR"
PYTHONUNBUFFERED=1 PROBE_RANK=2560 PROBE_OUT=1225_control_results.json \
  /home/peter/.local/bin/uv run --with numpy --with scipy --with mpmath \
  python "$PROOF/1225_positive_control_probe.py" \
  > "$LOGDIR/1225_official3.log" 2>&1
echo "official exit $?"
