#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  run_resource_aware_task.sh [options] -- command [args...]

Options:
  --class auto|normal|heavy  Requested resource class (default: auto).
  --workspace PATH           WSL build mirror (default: current directory).
  --mirror-key NAME          Stable lock name (default: hash of workspace).
  --wait SECONDS             Lock wait timeout (default: 3600).
  --log PATH                 Redirect command output after locks are held.
  --dry-run                  Print the decision without locking or running.
  --help                     Show this help.

Normal tasks take a shared global resource lock. Heavy tasks take the same
lock exclusively. Every task also takes an exclusive per-mirror lock so two
commands never write one .lake/build concurrently.
EOF
}

die() {
  printf 'resource-runner error: %s\n' "$*" >&2
  exit 2
}

requested_class=auto
workspace=
mirror_key=
wait_seconds=3600
log_path=
dry_run=0

while (($# > 0)); do
  case "$1" in
    --class)
      (($# >= 2)) || die '--class requires a value'
      requested_class=$2
      shift 2
      ;;
    --workspace)
      (($# >= 2)) || die '--workspace requires a value'
      workspace=$2
      shift 2
      ;;
    --mirror-key)
      (($# >= 2)) || die '--mirror-key requires a value'
      mirror_key=$2
      shift 2
      ;;
    --wait)
      (($# >= 2)) || die '--wait requires a value'
      wait_seconds=$2
      shift 2
      ;;
    --log)
      (($# >= 2)) || die '--log requires a value'
      log_path=$2
      shift 2
      ;;
    --dry-run)
      dry_run=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

case "$requested_class" in
  auto|normal|heavy) ;;
  *) die "invalid resource class: $requested_class" ;;
esac
[[ "$wait_seconds" =~ ^[0-9]+$ ]] || die '--wait must be a nonnegative integer'
(($# > 0)) || die 'missing command after --'

command=("$@")
if [[ -z "$workspace" ]]; then
  workspace=$PWD
fi
[[ -d "$workspace" ]] || die "workspace does not exist: $workspace"
workspace=$(realpath "$workspace")

if [[ -z "$mirror_key" ]]; then
  mirror_key=$(printf '%s' "$workspace" | sha256sum | cut -c1-16)
fi
mirror_key=${mirror_key//[^a-zA-Z0-9_.-]/_}
[[ -n "$mirror_key" ]] || die 'mirror key is empty after sanitization'

reasons=()
forced_heavy=0
auto_class=heavy
is_lake=0
lake_build_index=-1
is_numeric=0
command_name=

for ((i = 0; i < ${#command[@]}; i++)); do
  token=${command[$i]}
  base=${token##*/}
  lower=${base,,}
  case "$lower" in
    lake)
      is_lake=1
      ;;
    python|python3|uv)
      is_numeric=1
      ;;
  esac
  if ((is_lake == 1)) && [[ "${token,,}" == build ]] && ((lake_build_index < 0)); then
    lake_build_index=$i
  fi
  if [[ -z "$command_name" ]]; then
    case "$lower" in
      env|command|nice|time|timeout|flock) ;;
      -*|*=*) ;;
      *) command_name=$lower ;;
    esac
  fi
done

joined=$(printf '%s ' "${command[@]}")
joined_lower=${joined,,}

if ((is_lake == 1)); then
  if [[ ! -d "$workspace/.lake/build/lib/lean/ConnesWeilRH" ||
        ! -d "$workspace/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ]]; then
    forced_heavy=1
    reasons+=('cold Lean mirror: project or Mathlib olean tree is missing')
  fi

  if [[ "$joined_lower" == *' clean '* || "$joined_lower" == *' update '* ]]; then
    forced_heavy=1
    reasons+=('Lake clean/update operation')
  elif ((lake_build_index >= 0)); then
    targets=()
    for ((i = lake_build_index + 1; i < ${#command[@]}; i++)); do
      token=${command[$i]}
      [[ "$token" == -* || "$token" == *=* ]] && continue
      targets+=("$token")
    done
    if ((${#targets[@]} == 0)); then
      forced_heavy=1
      reasons+=('Lake build without an explicit target')
    else
      for target in "${targets[@]}"; do
        case "$target" in
          ConnesWeilRH|all|*Aggregate*|*FullRoot*|*UnifiedRemainingGaps*|*RhOutputAxiomLedger*)
            forced_heavy=1
            reasons+=("aggregate/root target: $target")
            ;;
        esac
      done
      if ((${#targets[@]} > 4)); then
        forced_heavy=1
        reasons+=("broad Lake batch: ${#targets[@]} explicit targets")
      elif ((forced_heavy == 0)); then
        auto_class=normal
        reasons+=("focused warm Lake build: ${#targets[@]} explicit target(s)")
      fi
    fi
  elif [[ "$joined_lower" == *' env lean '* || "$joined_lower" == *' env /'*'/lean '* ]]; then
    auto_class=normal
    reasons+=('focused lake env lean invocation')
  else
    reasons+=('unrecognized Lake operation')
  fi
elif ((is_numeric == 1)) &&
    [[ "$joined_lower" =~ (numpy|scipy|torch|jax|tensorflow|probe|sweep|benchmark|train|grid|certificate) ]]; then
  forced_heavy=1
  reasons+=('numeric/probe command may consume all BLAS or worker threads')
else
  case "$command_name" in
    rg|sed|cat|head|tail|wc|sha256sum|md5sum|true|printf)
      auto_class=normal
      reasons+=("known lightweight command: $command_name")
      ;;
    git)
      if [[ "$joined_lower" =~ [[:space:]](clone|fetch|pull|gc|repack|maintenance|submodule|lfs)[[:space:]] ]]; then
        forced_heavy=1
        reasons+=('broad Git network, maintenance, or object-store operation')
      else
        auto_class=normal
        reasons+=('local Git metadata or worktree operation')
      fi
      ;;
    bash|sh)
      if [[ "$joined_lower" == *' -n '* || "$joined_lower" == *' --version '* ]]; then
        auto_class=normal
        reasons+=("shell syntax/version check: $command_name")
      else
        reasons+=('shell payload cannot be inspected safely')
      fi
      ;;
    *)
      reasons+=("unknown command class: ${command_name:-unresolved}")
      ;;
  esac
fi

if ((forced_heavy == 1)); then
  resource_class=heavy
elif [[ "$requested_class" == heavy ]]; then
  resource_class=heavy
  reasons+=('explicit heavy request')
elif [[ "$requested_class" == normal ]]; then
  resource_class=normal
  reasons+=('explicit normal request')
else
  resource_class=$auto_class
fi

mem_total_kb=0
mem_available_kb=0
if [[ -r /proc/meminfo ]]; then
  read -r mem_total_kb mem_available_kb < <(
    awk '
      /^MemTotal:/ { total = $2 }
      /^MemAvailable:/ { available = $2 }
      END { print total + 0, available + 0 }
    ' /proc/meminfo
  )
fi
cpu_count=$(nproc 2>/dev/null || printf '1')
load_one=$(awk '{ print $1 }' /proc/loadavg 2>/dev/null || printf '0')

min_available_gib=${RH_RESOURCE_MIN_AVAILABLE_GIB:-6}
min_available_percent=${RH_RESOURCE_MIN_AVAILABLE_PERCENT:-20}
max_shared_load_ratio=${RH_RESOURCE_MAX_SHARED_LOAD_RATIO:-0.70}

if [[ "$resource_class" == normal ]] && ((mem_total_kb > 0)); then
  if awk -v available="$mem_available_kb" -v minimum="$min_available_gib" \
      'BEGIN { exit !(available < minimum * 1024 * 1024) }'; then
    resource_class=heavy
    reasons+=("low available memory: threshold ${min_available_gib} GiB")
  elif awk -v available="$mem_available_kb" -v total="$mem_total_kb" \
      -v minimum="$min_available_percent" \
      'BEGIN { exit !(100 * available / total < minimum) }'; then
    resource_class=heavy
    reasons+=("low available memory: threshold ${min_available_percent}%")
  fi
fi

if [[ "$resource_class" == normal ]] &&
    awk -v load_value="$load_one" -v cpus="$cpu_count" \
      -v maximum="$max_shared_load_ratio" \
      'BEGIN { exit !(cpus > 0 && load_value / cpus > maximum) }'; then
  resource_class=heavy
  reasons+=("high system load: shared threshold ${max_shared_load_ratio} per CPU")
fi

if [[ "$resource_class" == heavy ]]; then
  lock_mode=exclusive
else
  lock_mode=shared
fi

available_gib=$(awk -v value="$mem_available_kb" 'BEGIN { printf "%.2f", value / 1024 / 1024 }')
available_percent=$(awk -v available="$mem_available_kb" -v total="$mem_total_kb" \
  'BEGIN { if (total > 0) printf "%.1f", 100 * available / total; else printf "0.0" }')
load_ratio=$(awk -v load_value="$load_one" -v cpus="$cpu_count" \
  'BEGIN { if (cpus > 0) printf "%.2f", load_value / cpus; else printf "0.00" }')

printf 'RESOURCE_DECISION class=%s lock=%s requested=%s\n' \
  "$resource_class" "$lock_mode" "$requested_class"
printf 'RESOURCE_WORKSPACE path=%s mirror_key=%s\n' "$workspace" "$mirror_key"
printf 'RESOURCE_SNAPSHOT available_gib=%s available_percent=%s load_per_cpu=%s cpus=%s\n' \
  "$available_gib" "$available_percent" "$load_ratio" "$cpu_count"
for reason in "${reasons[@]}"; do
  printf 'RESOURCE_REASON %s\n' "$reason"
done

if ((dry_run == 1)); then
  exit 0
fi

command -v flock >/dev/null 2>&1 || die 'flock is required'
lock_dir=${RH_RESOURCE_LOCK_DIR:-/tmp/connes-weil-rh-resource-locks}
mkdir -p "$lock_dir"
admission_lock="$lock_dir/admission.lock"
resource_lock="$lock_dir/resource.lock"
mirror_lock="$lock_dir/mirror-$mirror_key.lock"

exec {admission_fd}>"$admission_lock"
flock -x -w "$wait_seconds" "$admission_fd" ||
  die "timed out waiting for admission lock after ${wait_seconds}s"

exec {resource_fd}>"$resource_lock"
if [[ "$resource_class" == heavy ]]; then
  flock -x -w "$wait_seconds" "$resource_fd" ||
    die "timed out waiting for exclusive resource lock after ${wait_seconds}s"
else
  flock -s -w "$wait_seconds" "$resource_fd" ||
    die "timed out waiting for shared resource lock after ${wait_seconds}s"
fi

# A heavy waiter holds admission until existing shared holders drain. This
# prevents a stream of new normal tasks from starving the exclusive task.
flock -u "$admission_fd"

exec {mirror_fd}>"$mirror_lock"
flock -x -w "$wait_seconds" "$mirror_fd" ||
  die "timed out waiting for mirror lock after ${wait_seconds}s"

cd "$workspace"
if [[ -n "$log_path" ]]; then
  mkdir -p "$(dirname "$log_path")"
  set +e
  "${command[@]}" >"$log_path" 2>&1
  command_exit=$?
  set -e
  printf 'RESOURCE_RESULT exit=%s log=%s\n' "$command_exit" "$log_path"
else
  set +e
  "${command[@]}"
  command_exit=$?
  set -e
  printf 'RESOURCE_RESULT exit=%s\n' "$command_exit"
fi
exit "$command_exit"
