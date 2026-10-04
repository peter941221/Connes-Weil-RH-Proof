#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
# One resource-runner lease; warm imports before the matched tactic timings.
/usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteABatchBaseline2552.lean \
  > build-logs/2567_baseline.log 2>&1
for tactic in Cbv Decide Rfl; do
  /usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
    "ConnesWeilRH/Dev/C1RouteAReplayProbe${tactic}2567.lean" \
    > "build-logs/2567_${tactic}.log" 2>&1
done
