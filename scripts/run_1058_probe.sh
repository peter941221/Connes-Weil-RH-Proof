#!/bin/bash
# Install mpmath (user site, proxy via WSL default gateway because localhost
# proxies are not mirrored into WSL NAT) and run the 1058 alpha probe,
# logging on the linux side per AGENTS 7a.
# System python3 is PEP 668 externally managed; the repo's probe environment
# is /home/peter/venv-46937-py312 (mpmath + numpy + scipy present).
PY=/home/peter/venv-46937-py312/bin/python
"$PY" -c "import mpmath, numpy" || { echo "MISSING_DEPS"; exit 2; }
LOG=/home/peter/cc20/probe1058.log
"$PY" /mnt/c/Projects/Connes-Weil-RH-Proof/docs/proofs/1058_alpha_chi_reconnaissance_probe.py > "$LOG" 2>&1
echo "written bytes: $(wc -c < "$LOG")"
