#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
cache_root=${NANODA_CACHE_ROOT-"$repo_root/.lake"}
if [[ -z "$cache_root" ]]; then
  printf '%s\n' 'NANODA_CACHE_ROOT must name a nonempty directory' >&2
  exit 2
fi
cache_root=$(realpath -m -- "$cache_root")
lake_runner="$repo_root/scripts/run-lake.sh"
config="$repo_root/scripts/nanoda/config.json"
# Retired knobs must not silently select a different producer or proof scope.
for retired in LEAN4EXPORT_BIN NANODA_EXPORT_MODE NANODA_SHARDS NANODA_CHUNK_ROOTS \
    NANODA_MAX_EXPRS NANODA_MAX_BYTES NANODA_HARD_ROOTS NANODA_HARD_EXPRS NANODA_HARD_BYTES; do
  if [[ -v "$retired" ]]; then
    printf '%s is retired; native export uses one compatible graph and isolated script environments\n' "$retired" >&2
    exit 2
  fi
done
nanoda_bin=${NANODA_BIN:-}
if [[ -z "$nanoda_bin" ]]; then
  nanoda_bin="$repo_root/.external/nanoda/target/release/nanoda_bin"
  if [[ ! -x "$nanoda_bin" ]]; then nanoda_bin=$(command -v nanoda_bin || true); fi
fi
if [[ -z "$nanoda_bin" || ! -x "$nanoda_bin" ]]; then
  printf '%s\n' 'missing nanoda: set NANODA_BIN or build the pinned source under .external/nanoda' >&2
  exit 1
fi
nanoda_bin=$(realpath -- "$nanoda_bin")
# The pinned parallel checker uses its normal worker stacks; the serial path
# checks on the smaller main-thread stack. Two threads are the measured default.
nanoda_jobs=${NANODA_JOBS:-2}
nanoda_export_jobs=${NANODA_EXPORT_JOBS:-3}
nanoda_checks=${NANODA_POST_EXPORT_CHECKS:-3}
for setting in NANODA_JOBS NANODA_EXPORT_JOBS NANODA_POST_EXPORT_CHECKS; do
  case "$setting" in
    NANODA_JOBS) value=$nanoda_jobs ;;
    NANODA_EXPORT_JOBS) value=$nanoda_export_jobs ;;
    NANODA_POST_EXPORT_CHECKS) value=$nanoda_checks ;;
  esac
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    printf '%s must be a positive integer (received: %s)\n' "$setting" "$value" >&2
    exit 2
  fi
done
nanoda_pipeline=${NANODA_PIPELINE:-1}
if [[ "$nanoda_pipeline" != 0 && "$nanoda_pipeline" != 1 ]]; then
  printf '%s\n' 'NANODA_PIPELINE must be 0 or 1' >&2
  exit 2
fi
modules_file=$(mktemp "${TMPDIR:-/tmp}/ccl-nanoda-modules.XXXXXX")
nanoda_dir=$(mktemp -d "${TMPDIR:-/tmp}/ccl-nanoda.XXXXXX")
pipeline_pid=
cleanup_nanoda() {
  if [[ -n "$pipeline_pid" ]] && kill -0 "$pipeline_pid" 2>/dev/null; then
    kill -TERM "$pipeline_pid" 2>/dev/null || true
    wait "$pipeline_pid" || true
  fi
  rm -f -- "$modules_file"
  rm -rf -- "$nanoda_dir"
}
trap cleanup_nanoda EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
if [[ -n "${NANODA_MODULE_MANIFEST:-}" ]]; then
  cp -- "$NANODA_MODULE_MANIFEST" "$modules_file"
else
  python3 "$repo_root/scripts/project-modules.py" --configured-scripts > "$modules_file"
fi
mapfile -t modules < "$modules_file"
if (( ${#modules[@]} == 0 )); then
  printf '%s\n' 'nanoda check found no active project Lean modules' >&2
  exit 1
fi
declare -A seen_modules=()
for module in "${modules[@]}"; do
  if [[ -z "$module" || -v seen_modules[$module] ]]; then
    printf 'nanoda module manifest has an empty or repeated module: %s\n' "$module" >&2
    exit 1
  fi
  seen_modules[$module]=1
done
# Suppress successful export-info log replay; warnings and failures remain fatal.
"$lake_runner" --quiet --wfail build "${modules[@]}" >/dev/null
lean_path=$("$lake_runner" env printenv LEAN_PATH)
lean_sysroot=$("$lake_runner" env lean --print-prefix)
export LEAN_PATH="$lean_path" LEAN_SYSROOT="$lean_sysroot"
export PATH="$lean_sysroot/bin:$PATH"
python3 - "$config" "$nanoda_dir/config.json" "$nanoda_jobs" <<'PY_CONFIG'
import json, sys
from pathlib import Path
settings = json.loads(Path(sys.argv[1]).read_text())
settings['num_threads'] = int(sys.argv[3])
Path(sys.argv[2]).write_text(json.dumps(settings, sort_keys=True) + '\n')
PY_CONFIG
args=(--manifest "$modules_file" --cache "$cache_root" --checker "$nanoda_bin" \
  --config "$nanoda_dir/config.json" --exporters "$nanoda_export_jobs" --checkers "$nanoda_checks")
if [[ "$nanoda_pipeline" == 0 ]]; then args+=(--sequential); fi
printf 'nanoda: native exporters=%s, checker instances=%s, threads per checker=%s\n' \
  "$nanoda_export_jobs" "$nanoda_checks" "$nanoda_jobs" >&2
python3 -m scripts.nanoda.pipeline "${args[@]}" &
pipeline_pid=$!
wait "$pipeline_pid"
pipeline_pid=
