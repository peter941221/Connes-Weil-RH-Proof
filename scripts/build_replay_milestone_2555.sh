#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == --matched ]]; then
  bash scripts/run_kernel_matched_nodes_2555.sh
fi
targets=(ConnesWeilRH)
for file in ConnesWeilRH/Dev/C1RouteA*255{2,3,4,5}.lean; do
  [[ -f $file ]] || continue
  module=${file%.lean}
  targets+=("${module//\//.}")
done
"${LEAN_LAKE:-lake}" build "${targets[@]}"
