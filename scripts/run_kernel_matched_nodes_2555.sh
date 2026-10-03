#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
/usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteABatchBaseline2552.lean \
  > build-logs/2555_matched_nodes_baseline.log 2>&1
for name in N02701Minus N05440Plus; do
  for method in Paired Kernel; do
    record=2553
    if [[ $method == Kernel ]]; then record=2555; fi
    /usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
      "ConnesWeilRH/Dev/C1RouteA${method}${name}${record}.lean" \
      > "build-logs/2555_matched_${method}_${name}.log" 2>&1
  done
done
