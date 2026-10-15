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

# A failed build can leave several hundred GB of intermediate IR.  Refuse to
# start when the native filesystem cannot absorb one bounded entry plus OS
# headroom.  The threshold is deliberately explicit and easy to override in
# a controlled environment.
min_free_gib=${MIN_FREE_GIB:-8}
free_kib=$(df -Pk "$root" | awk 'NR==2 {print $4}')
min_free_kib=$((min_free_gib * 1024 * 1024))
if [[ -z "$free_kib" || "$free_kib" -lt "$min_free_kib" ]]; then
  echo "refusing build: ${free_kib:-unknown} KiB free; need ${min_free_gib} GiB" >&2
  exit 3
fi
echo "preflight: ${free_kib} KiB free (threshold ${min_free_kib} KiB)"

flock -w 60 /tmp/connes-weil-rh-lake.lock \
  lake build -Kjobs=2 "$target"

# The pruner re-checks every source and assembly digest before deleting any
# generated output.  A failed provenance check leaves the build intact.
python3 scripts/prune_on_verify_2664.py "$1" "$2" --apply

echo "completed and pruned entry (${1},${2}): ${target}"
