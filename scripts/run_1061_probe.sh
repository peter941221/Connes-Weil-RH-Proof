#!/bin/bash
# 1061 alpha campaign slice T1: mpmath candidate eigenvalue table for the
# paper's lambda(n) (even branch, c = 2 pi).  Interpreter policy per AGENTS
# 7a: /home/peter/venv-46937-py312 (mpmath + numpy + scipy present; system
# python3 is PEP 668 externally managed).  Log lands on the linux side in
# HOME, not /tmp (tmpfs is wiped between harness calls).
PY=/home/peter/venv-46937-py312/bin/python
"$PY" -c "import mpmath, numpy" || { echo "MISSING_DEPS"; exit 2; }
LOG=/home/peter/cc20/probe1061.log
"$PY" /mnt/c/Projects/Connes-Weil-RH-Proof/docs/proofs/1061_alpha_lambda_t1_probe.py > "$LOG" 2>&1
echo "written bytes: $(wc -c < "$LOG")"
