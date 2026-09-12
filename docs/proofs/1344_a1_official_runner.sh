#!/bin/bash
# Record 1344 A1 OFFICIAL runner (batch 1547).
# Sequence: anchor G1a/G1b + G8c (once) -> m=24 verbatim-path Gram +
# REPRODUCE gate -> G9 path-equivalence -> m=48/96 fast prime path ->
# doubling m=24 at 2x NQ (verbatim) -> alpha fit + preregistered branches.
# Fidelity pins: numpy==2.5.3 / mpmath==1.4.1 - the committed 1342 digits
# (lambda_min +3.0832438870712037e-03) were produced under those versions;
# environment drift would attack the REPRODUCE gate (amendment 3a).
# Acceptance is by LOG CONTENT ("DONE 1344-A1" sentinel), not exit code.
set -u
PROOF=/home/peter/rh/docs/proofs
LOGDIR=$PROOF/1344_logs
mkdir -p "$LOGDIR"
cd "$PROOF" || exit 1
PYTHONUNBUFFERED=1 P_OUT=1344_a1_results.json \
  /home/peter/.local/bin/uv run --no-project \
  --with numpy==2.5.3 --with scipy --with mpmath==1.4.1 \
  python "$PROOF/1344_a1_m_scaling_probe.py" \
  > "$LOGDIR/1547_1344_a1_official.log" 2>&1
echo "official exit $?"
tail -n 16 "$LOGDIR/1547_1344_a1_official.log"
echo RUNNER_DONE
