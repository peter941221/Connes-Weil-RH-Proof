#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
/usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteABatchBaseline2552.lean \
  > build-logs/2555_baseline.log 2>&1
/usr/bin/time -v "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteABatchPaired2552.lean \
  > build-logs/2555_control.log 2>&1
/usr/bin/time -v timeout 120 "${LEAN_LAKE:-lake}" env lean \
  ConnesWeilRH/Dev/C1RouteAKernelTrial2555.lean \
  > build-logs/2555_kernel.log 2>&1
