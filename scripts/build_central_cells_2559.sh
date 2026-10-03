#!/usr/bin/env bash
set -euo pipefail
# Each cell builds its own new dependencies while sharing previously checked
# nodes. Limit concurrent heavy dependency groups by building cells in order.
for sign in Plus Minus; do
  for index in 05119 05120; do
    /usr/bin/time -f "CENTRAL_CELL index=${index} sign=${sign} elapsed=%e user=%U system=%S peak_kib=%M" \
      "${LEAN_LAKE:-lake}" build "ConnesWeilRH.Dev.C1RouteABatchC${index}${sign}Integral2559"
  done
done
