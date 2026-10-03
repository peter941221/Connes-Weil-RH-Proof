#!/usr/bin/env bash
set -euo pipefail

# Invoke inside one resource-runner lease. Keep one WSL session alive so
# startup/page-cache differences are visible in the two baseline readings.
mkdir -p build-logs
for mode in Baseline Paired Separate BaselineWarm; do
  stem=$mode
  if [[ $mode == BaselineWarm ]]; then stem=Baseline; fi
  /usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
    "ConnesWeilRH/Dev/C1RouteABatch${stem}2552.lean" \
    > "build-logs/2552_${mode,,}.log" 2>&1
done
