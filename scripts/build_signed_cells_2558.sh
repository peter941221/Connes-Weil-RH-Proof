#!/usr/bin/env bash
set -euo pipefail
targets=()
for file in ConnesWeilRH/Dev/C1RouteABatch*2558.lean; do
  module=${file%.lean}
  targets+=("${module//\//.}")
done
/usr/bin/time -f 'SIGNED_CELL_BUILD elapsed=%e user=%U system=%S peak_kib=%M' \
  "${LEAN_LAKE:-lake}" build "${targets[@]}"
