#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
runner="$script_dir/run_resource_aware_task.sh"
tmp_dir=$(mktemp -d /tmp/connes-weil-resource-test.XXXXXX)
case "$tmp_dir" in
  /tmp/connes-weil-resource-test.*) ;;
  *) printf 'unexpected temporary directory: %s\n' "$tmp_dir" >&2; exit 2 ;;
esac
cleanup() {
  rm -rf -- "$tmp_dir"
}
trap cleanup EXIT

warm="$tmp_dir/warm"
cold="$tmp_dir/cold"
mkdir -p "$warm/.lake/build/lib/lean/ConnesWeilRH"
mkdir -p "$warm/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib"
mkdir -p "$cold"

classify() {
  local expected=$1
  local workspace=$2
  shift 2
  local output
  output=$(
    RH_RESOURCE_MIN_AVAILABLE_GIB=0 \
    RH_RESOURCE_MIN_AVAILABLE_PERCENT=0 \
    RH_RESOURCE_MAX_SHARED_LOAD_RATIO=999 \
      "$runner" --dry-run --workspace "$workspace" -- "$@"
  )
  printf '%s\n' "$output"
  grep -q "RESOURCE_DECISION class=$expected " <<<"$output" || {
    printf 'expected class=%s\n' "$expected" >&2
    exit 1
  }
}

classify normal "$warm" /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Dev.C1CC20EndpointEigenvalueTail983 \
  ConnesWeilRH.Dev.C1CC20EndpointEigenvalueTail983Audit
classify heavy "$warm" /home/peter/.elan/bin/lake build ConnesWeilRH
classify heavy "$cold" /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Dev.C1CC20EndpointEigenvalueTail983
classify heavy "$warm" /home/peter/.local/bin/uv run --with numpy --with scipy \
  python alpha_certificate_probe.py
classify normal "$warm" rg -n eigenvalue_sq_lt_one ConnesWeilRH
classify normal "$warm" git status --short
classify heavy "$warm" git gc
classify heavy "$warm" bash opaque_task.sh

pressure_output=$(
  RH_RESOURCE_MIN_AVAILABLE_GIB=999999 \
  RH_RESOURCE_MIN_AVAILABLE_PERCENT=0 \
  RH_RESOURCE_MAX_SHARED_LOAD_RATIO=999 \
    "$runner" --dry-run --workspace "$warm" -- \
      rg -n eigenvalue_sq_lt_one ConnesWeilRH
)
printf '%s\n' "$pressure_output"
grep -q 'RESOURCE_DECISION class=heavy ' <<<"$pressure_output" || {
  printf 'resource pressure did not upgrade a normal task to heavy\n' >&2
  exit 1
}
grep -q 'RESOURCE_REASON low available memory' <<<"$pressure_output" || {
  printf 'resource pressure upgrade did not report its reason\n' >&2
  exit 1
}

lock_dir="$tmp_dir/locks"
run_sleep() {
  local class=$1
  local key=$2
  RH_RESOURCE_MIN_AVAILABLE_GIB=0 \
  RH_RESOURCE_MIN_AVAILABLE_PERCENT=0 \
  RH_RESOURCE_MAX_SHARED_LOAD_RATIO=999 \
  RH_RESOURCE_LOCK_DIR="$lock_dir" \
    "$runner" --class "$class" --workspace "$warm" --mirror-key "$key" \
      --wait 10 -- /bin/sleep 1 >/dev/null
}

elapsed_pair_ms() {
  local first_class=$1
  local first_key=$2
  local second_class=$3
  local second_key=$4
  local start end
  start=$(date +%s%3N)
  run_sleep "$first_class" "$first_key" &
  first_pid=$!
  run_sleep "$second_class" "$second_key" &
  second_pid=$!
  wait "$first_pid"
  wait "$second_pid"
  end=$(date +%s%3N)
  printf '%s' "$((end - start))"
}

parallel_ms=$(elapsed_pair_ms normal mirror-a normal mirror-b)
((parallel_ms < 1800)) || {
  printf 'normal tasks on different mirrors did not overlap: %sms\n' "$parallel_ms" >&2
  exit 1
}

same_mirror_ms=$(elapsed_pair_ms normal mirror-a normal mirror-a)
((same_mirror_ms >= 1800)) || {
  printf 'same-mirror tasks were not serialized: %sms\n' "$same_mirror_ms" >&2
  exit 1
}

exclusive_ms=$(elapsed_pair_ms heavy mirror-a normal mirror-b)
((exclusive_ms >= 1800)) || {
  printf 'heavy task did not exclude a normal task: %sms\n' "$exclusive_ms" >&2
  exit 1
}

event_log="$tmp_dir/writer-priority.events"
run_marked() {
  local class=$1
  local key=$2
  local label=$3
  local delay=$4
  RH_RESOURCE_MIN_AVAILABLE_GIB=0 \
  RH_RESOURCE_MIN_AVAILABLE_PERCENT=0 \
  RH_RESOURCE_MAX_SHARED_LOAD_RATIO=999 \
  RH_RESOURCE_LOCK_DIR="$lock_dir" \
    "$runner" --class "$class" --workspace "$warm" --mirror-key "$key" \
      --wait 10 -- /bin/bash -c \
      'printf "%s-start\n" "$1" >> "$2"; sleep "$3"; printf "%s-end\n" "$1" >> "$2"' \
      _ "$label" "$event_log" "$delay" >/dev/null
}

run_marked normal priority-holder holder 1 &
holder_pid=$!
for _ in $(seq 1 100); do
  [[ -s "$event_log" ]] && break
  sleep 0.01
done
[[ -s "$event_log" ]] || {
  printf 'normal holder did not acquire the resource lock\n' >&2
  exit 1
}

run_marked heavy priority-heavy heavy 0.2 &
heavy_pid=$!
admission_blocked=0
for _ in $(seq 1 100); do
  if ! flock -n "$lock_dir/admission.lock" true; then
    admission_blocked=1
    break
  fi
  sleep 0.01
done
((admission_blocked == 1)) || {
  printf 'heavy waiter did not hold the admission lock\n' >&2
  exit 1
}

run_marked normal priority-follower follower 0.1 &
follower_pid=$!
wait "$holder_pid"
wait "$heavy_pid"
wait "$follower_pid"

mapfile -t priority_events < "$event_log"
expected_events=(holder-start holder-end heavy-start heavy-end follower-start follower-end)
[[ "${priority_events[*]}" == "${expected_events[*]}" ]] || {
  printf 'heavy waiter priority failed\nexpected: %s\nactual:   %s\n' \
    "${expected_events[*]}" "${priority_events[*]}" >&2
  exit 1
}

printf 'lock tests: shared=%sms same-mirror=%sms exclusive=%sms\n' \
  "$parallel_ms" "$same_mirror_ms" "$exclusive_ms"
printf 'writer priority: %s\n' "${priority_events[*]}"
printf 'resource-aware task classifier tests passed\n'
