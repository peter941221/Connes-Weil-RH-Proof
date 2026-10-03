#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
# Run under one resource-runner lease. Each invocation checks real source.
for node in 02700 02701 05440 10239; do
  for sign in Plus Minus; do
    name="N${node}${sign}"
    /usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
      "ConnesWeilRH/Dev/C1RouteAPaired${name}2553.lean" \
      > "build-logs/2553_${name}.log" 2>&1
  done
done
