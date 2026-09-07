#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
lake_runner="$repo_root/scripts/run-lake.sh"
config="$repo_root/scripts/nanoda-config.json"
exporter_source="$repo_root/scripts/ProjectNanodaExport.lean"

lean4export_bin=${LEAN4EXPORT_BIN:-}
if [[ -z "$lean4export_bin" ]]; then
  local_lean4export="$repo_root/.external/lean4export/.lake/build/bin/lean4export"
  if [[ -x "$local_lean4export" ]]; then
    lean4export_bin=$local_lean4export
  else
    lean4export_bin=$(command -v lean4export || true)
  fi
fi

nanoda_bin=${NANODA_BIN:-}
if [[ -z "$nanoda_bin" ]]; then
  local_nanoda="$repo_root/.external/nanoda/target/release/nanoda_bin"
  if [[ -x "$local_nanoda" ]]; then
    nanoda_bin=$local_nanoda
  else
    nanoda_bin=$(command -v nanoda_bin || true)
  fi
fi

if [[ -z "$lean4export_bin" || ! -x "$lean4export_bin" ]]; then
  printf '%s\n' \
    'missing lean4export: set LEAN4EXPORT_BIN or build the pinned source under .external/lean4export' >&2
  exit 1
fi

if [[ -z "$nanoda_bin" || ! -x "$nanoda_bin" ]]; then
  printf '%s\n' \
    'missing nanoda: set NANODA_BIN or build the pinned source under .external/nanoda' >&2
  exit 1
fi

available_cpus=$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf '%s\n' 1)
if [[ ! "$available_cpus" =~ ^[1-9][0-9]*$ ]]; then
  available_cpus=1
fi
nanoda_jobs=${NANODA_JOBS:-$available_cpus}
if [[ ! "$nanoda_jobs" =~ ^[1-9][0-9]*$ ]]; then
  printf 'NANODA_JOBS must be a positive integer (received: %s)\n' "$nanoda_jobs" >&2
  exit 1
fi

export_metadata=$("$lake_runner" env "$lean4export_bin" --help)
lean_version=$("$lake_runner" env lean --version | sed -n 's/.*version \([^, ]*\).*/\1/p')
if [[ -z "$lean_version" || "$export_metadata" != *"\"version\":\"$lean_version\""* ]]; then
  printf '%s\n' 'lean4export was not built for the repository Lean version' >&2
  printf '%s\n' "$export_metadata" >&2
  exit 1
fi

declare -a modules=()
while IFS= read -r source; do
  relative=${source#"$repo_root/"}
  module=${relative%.lean}
  modules+=("${module//\//.}")
done < <(
  find "$repo_root" \
    \( -path "$repo_root/.git" \
      -o -path "$repo_root/.lake" \
      -o -path "$repo_root/.elan" \
      -o -path "$repo_root/.external" \
      -o -path "$repo_root/legacy" \
      -o -path "$repo_root/scripts" \
      -o -path "$repo_root/mathlib/RFAP/LegacyQuotientFraction.lean" \) \
    -prune -o -type f -name '*.lean' -print | sort -u
)

if (( ${#modules[@]} == 0 )); then
  printf '%s\n' 'nanoda check found no active project Lean modules' >&2
  exit 1
fi

# Building the exact discovered module set both enforces warning-free sources
# and ensures that the compiled metadata exported below is current.
"$lake_runner" --wfail build "${modules[@]}" >/dev/null

nanoda_dir=$(mktemp -d "${TMPDIR:-/tmp}/ccl-nanoda.XXXXXX")
module_manifest="$nanoda_dir/modules.txt"
export_overlay="$nanoda_dir/object-overlay"
runtime_config="$nanoda_dir/config.json"
cleanup_nanoda() {
  rm -rf -- "$nanoda_dir"
}
trap cleanup_nanoda EXIT HUP INT TERM

printf '%s\n' "${modules[@]}" > "$module_manifest"
sed "s/\"num_threads\": 1/\"num_threads\": $nanoda_jobs/" \
  "$config" > "$runtime_config"
mkdir -p "$export_overlay"

link_object_tree() {
  local source_root=$1
  local target_root=$2
  local source_path relative target

  while IFS= read -r source_path; do
    relative=${source_path#"$source_root"}
    mkdir -p "$target_root$relative"
  done < <(find "$source_root" -type d -print)

  while IFS= read -r source_path; do
    relative=${source_path#"$source_root"/}
    target="$target_root/$relative"
    if [[ -e "$target" || -L "$target" ]]; then
      printf 'nanoda object overlay collision at %s\n' "$target" >&2
      return 1
    fi
    ln -s "$source_path" "$target"
  done < <(find "$source_root" \( -type f -o -type l \) -print)
}

# A single object prefix is required on case-insensitive filesystems because
# this project intentionally has lowercase `mathlib.*` modules beside upstream
# `Mathlib.*` modules.  The exporter source itself imports `Export` from the
# pinned lean4export build, so its object directory joins the same LEAN_PATH.
project_objects="$repo_root/.lake/build/lib/lean"
mathlib_objects="$repo_root/.lake/packages/mathlib/.lake/build/lib/lean"
exporter_objects=$(CDPATH= cd -- "$(dirname -- "$lean4export_bin")/../lib/lean" && pwd)
if [[ ! -d "$project_objects/mathlib" || ! -d "$mathlib_objects/Mathlib" ||
      ! -f "$exporter_objects/Export.olean" ]]; then
  printf '%s\n' 'missing built project, Mathlib, or lean4export objects' >&2
  exit 1
fi
link_object_tree "$project_objects/mathlib" "$export_overlay/mathlib"
link_object_tree "$mathlib_objects/Mathlib" "$export_overlay/Mathlib"

lake_lean_path=$("$lake_runner" env printenv LEAN_PATH)
export_lean_path="$export_overlay:$exporter_objects:$lake_lean_path"
printf 'nanoda: checking with %s worker threads\n' "$nanoda_jobs" >&2
report=$(
  "$lake_runner" env env LEAN_PATH="$export_lean_path" \
    lean --run "$exporter_source" "$module_manifest" |
    "$nanoda_bin" "$runtime_config"
)
printf '%s\n' "$report"

if [[ "$report" != *'Checked '*' declarations with no errors'* ]]; then
  printf '%s\n' 'nanoda did not report a clean repository-wide check' >&2
  exit 1
fi

axiom_count=$(printf '%s\n' "$report" | grep -c '^axiom ' || true)
if [[ "$axiom_count" -ne 1 ]] ||
    [[ "$report" != *'axiom propext '* ]] ||
    [[ "$report" == *'axiom Quot.sound.'* ]]; then
  printf '%s\n' 'nanoda admitted an unexpected repository-wide axiom set' >&2
  exit 1
fi
