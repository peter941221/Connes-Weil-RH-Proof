#!/usr/bin/env bash
set -eu

source_root=/mnt/c/Projects/Connes-Weil-RH-Proof
workspace=/home/peter/rh-native
result_dir="$source_root/results"
log=/tmp/routea_inactive_3320.log
audit=/tmp/routea_inactive_3320_audit.log
status=/tmp/routea_inactive_3320.status

finish() {
  code=$?
  printf '%s\n' "$code" > "$status"
  cp "$status" "$result_dir/3320_inactive.status"
  if test -f "$log"; then cp "$log" "$result_dir/3320_inactive.log"; fi
  if test -f "$audit"; then cp "$audit" "$result_dir/3320_inactive_audit.log"; fi
}
trap finish EXIT

: > "$log"
: > "$audit"
cd "$workspace"
cp "$source_root/lean-toolchain" lean-toolchain
cp "$source_root/ConnesWeilRH/Dev/C1RouteARationalSignedJetInactive3320.lean" ConnesWeilRH/Dev/
cp "$source_root/ConnesWeilRH/Dev/C1RouteARationalSignedJetInactive3320Audit.lean" ConnesWeilRH/Dev/
test "$(cat lean-toolchain)" = leanprover/lean4:v4.30.0
lean --version | grep -F 'version 4.30.0'
cat lean-toolchain
LEAN_NUM_THREADS=1 lake build ConnesWeilRH.Dev.C1RouteARationalSignedJetInactive3320 > "$log" 2>&1
LEAN_NUM_THREADS=1 lake env lean ConnesWeilRH/Dev/C1RouteARationalSignedJetInactive3320Audit.lean > "$audit" 2>&1
