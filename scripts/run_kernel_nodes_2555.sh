#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
/usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteABatchBaseline2552.lean \
  > build-logs/2555_nodes_baseline.log 2>&1
for node in 02700 02701 05440 10239; do
  for sign in Plus Minus; do
    name="N${node}${sign}"
    /usr/bin/time -v timeout 120 "${LEAN_LAKE:-lake}" env lean \
      "ConnesWeilRH/Dev/C1RouteAKernel${name}2555.lean" \
      > "build-logs/2555_${name}.log" 2>&1
  done
done
