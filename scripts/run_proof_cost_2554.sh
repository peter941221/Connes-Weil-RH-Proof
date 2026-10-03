#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
# One resource-runner lease; warm imports before cumulative phase timings.
/usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteABatchBaseline2552.lean \
  > build-logs/2554_baseline.log 2>&1
for mode in Replay Base Full; do
  /usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
    "ConnesWeilRH/Dev/C1RouteAProfile${mode}2554.lean" \
    > "build-logs/2554_${mode}.log" 2>&1
done
