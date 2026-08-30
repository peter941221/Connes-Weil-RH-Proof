#!/bin/bash
# 1062 alpha campaign slices T2/T3: sinc-extension modes and the
# endpointSlope anchor validation.  Interpreter policy per AGENTS 7a:
# /home/peter/venv-46937-py312.  Log in HOME, not /tmp (tmpfs wipe).
PY=/home/peter/venv-46937-py312/bin/python
"$PY" -c "import mpmath, numpy" || { echo "MISSING_DEPS"; exit 2; }
LOG=/home/peter/cc20/probe1062.log
"$PY" /mnt/c/Projects/Connes-Weil-RH-Proof/docs/proofs/1062_alpha_t2t3_mode_anchor_probe.py > "$LOG" 2>&1
echo "written bytes: $(wc -c < "$LOG")"
