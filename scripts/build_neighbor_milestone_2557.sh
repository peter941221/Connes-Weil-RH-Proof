#!/usr/bin/env bash
set -euo pipefail
targets=(ConnesWeilRH)
for file in ConnesWeilRH/Dev/C1RouteAShared*2556.lean ConnesWeilRH/Dev/C1RouteANeighbor*2557.lean; do
  module=${file%.lean}
  targets+=("${module//\//.}")
done
"${LEAN_LAKE:-lake}" build "${targets[@]}"
