#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 ROW COL" >&2
  exit 2
fi

row=$(printf '%02d' "$1")
col=$(printf '%02d' "$2")
target="ConnesWeilRH.Dev.OffDiagE${row}_${col}.C1RouteAEntryAssembly2663"

export PATH="${HOME}/.elan/bin:${PATH}"
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

flock -w 60 /tmp/connes-weil-rh-lake.lock \
  lake build -Kjobs=2 "$target"

# The pruner re-checks every source and assembly digest before deleting any
# generated output.  A failed provenance check leaves the build intact.
python3 scripts/prune_on_verify_2664.py "$1" "$2" --apply

echo "completed and pruned entry (${1},${2}): ${target}"
