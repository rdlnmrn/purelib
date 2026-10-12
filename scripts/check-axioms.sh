#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf '%s\n' \
    'Usage: scripts/check-axioms.sh [--no-build] [--configured-scripts] [--all-helpers] [--report-ir-only] [--full | MODULE_OR_FILE ...]' \
    'No targets (or --full): audit every active project module.' \
    'Targets: audit the named modules/files and their transitive axiom closures.' \
    'Default: select source-facing declarations and audit their complete transitive axiom closures.' \
    '--all-helpers also selects every retained meta/unsafe/partial/generated kernel helper as a root.' \
    '--report-ir-only adds an inventory of code without kernel declarations to AXIOM_AUDIT_REPORT_DIR; it is not an axiom check.' \
    '--configured-scripts also includes the harness/checkpoint roots declared to Lake.' \
    'Select affected consumers explicitly; reverse dependencies are not added.' \
    'The strict canonical audit, independent regression-owner audit and executable replay run in both modes.' \
    '--no-build requires current artifacts, including audit/regression prerequisites.' \
    'AXIOM_AUDIT_REPORT_DIR retains complete roots/dirty edges and disables pass reuse.'
}

# Avoid pinned Lake replaying synchronous export-info backtraces from successful logs.
# Quiet mode retains warning-fatal checking and all failure diagnostics.
build_options=(--quiet --wfail)
full=false
include_scripts=false
report_ir_only=false
all_helpers=false
declare -a targets=()
while (( $# )); do
  case "$1" in
    --no-build) build_options+=(--no-build) ;;
    --full) full=true ;;
    --configured-scripts) include_scripts=true ;;
    --report-ir-only) report_ir_only=true ;;
    --all-helpers) all_helpers=true ;;
    --help|-h) usage; exit 0 ;;
    --) shift; targets+=("$@"); break ;;
    -*) usage >&2; exit 2 ;;
    *) targets+=("$1") ;;
  esac
  shift
done
if [[ "$full" == true ]] && (( ${#targets[@]} )); then
  printf '%s\n' '--full cannot be combined with module/file targets' >&2
  exit 2
fi
if [[ "$report_ir_only" == true && -z "${AXIOM_AUDIT_REPORT_DIR:-}" ]]; then
  printf '%s\n' '--report-ir-only requires AXIOM_AUDIT_REPORT_DIR' >&2
  exit 2
fi

repo_dir="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
lake_runner="$repo_dir/scripts/run-lake.sh"

if command -v sha256sum >/dev/null 2>&1; then
  hash_program=sha256sum
elif command -v shasum >/dev/null 2>&1; then
  hash_program=shasum
else
  printf '%s\n' "axiom audit requires sha256sum or shasum" >&2
  exit 1
fi

hash_stream() {
  if [[ "$hash_program" == sha256sum ]]; then
    sha256sum | awk '{print $1}'
  else
    shasum -a 256 | awk '{print $1}'
  fi
}

declare -a modules=()
module_options=()
if [[ "$include_scripts" == true ]]; then module_options+=(--configured-scripts); fi
mapfile -t modules < <(python3 "$repo_dir/scripts/project-modules.py" "${module_options[@]}")

if (( ${#modules[@]} == 0 )); then
  printf '%s\n' "project axiom audit found no Lean modules" >&2
  exit 1
fi

# Keep the complete project boundary for provenance, even in a scoped worker.
all_modules=("${modules[@]}")
audit_scope=full
if (( ${#targets[@]} )); then
  audit_scope=scoped
  modules=()
  declare -A active_modules=()
  for module in "${all_modules[@]}"; do active_modules["$module"]=1; done
  for target in "${targets[@]}"; do
    if [[ "$target" == *.lean ]]; then
      if [[ ! -f "$target" ]]; then
        printf 'axiom audit: source does not exist: %s\n' "$target" >&2
        exit 2
      fi
      source_dir="$(CDPATH='' cd -- "$(dirname -- "$target")" && pwd -P)"
      source="$source_dir/$(basename -- "$target")"
      relative="${source#"$repo_dir/"}"
      target="${relative%.lean}"
      target="${target//\//.}"
    fi
    if [[ -z "$target" || -z "${active_modules[$target]:-}" ]]; then
      printf 'axiom audit: not an active project module: %s\n' "$target" >&2
      exit 2
    fi
    modules+=("$target")
  done
  mapfile -t modules < <(printf '%s\n' "${modules[@]}" | LC_ALL=C sort -u)
fi

# The worker imports a small fixed canonical surface even in scoped mode.
# Discover its project imports from the authoritative checker, not a second list.
mapfile -t audit_support < <(python3 "$repo_dir/scripts/project-module-data.py" audit-support)
if (( ${#audit_support[@]} == 0 )); then
  printf '%s\n' 'axiom audit found empty canonical support inventory' >&2
  exit 1
fi
cd "$repo_dir"
regression_module=$(python3 "$repo_dir/scripts/project-module-data.py" regression-root)
if [[ -z "$regression_module" ]] || ! printf '%s\n' "${all_modules[@]}" | LC_ALL=C grep -Fx -- "$regression_module" >/dev/null; then
  printf '%s\n' 'axiom audit: required regression owner is missing from the project inventory' >&2
  exit 1
fi
# The executable owner is mandatory support, audited in its own project environment.
mapfile -t modules < <(printf '%s\n' "${modules[@]}" "$regression_module" | LC_ALL=C sort -u)
printf 'axiom audit: %s scope, %s project modules\n' "$audit_scope" "${#modules[@]}"
# Lake checks the selected modules and their dependencies, not unrelated roots.
# Include every worker/regression prerequisite in this mandatory currentness gate.
build_log="$(mktemp "${TMPDIR:-/tmp}/ccl-axiom-build.XXXXXX")"
if "$lake_runner" "${build_options[@]}" build \
    "${modules[@]}" "${audit_support[@]}" fraction_regression >"$build_log" 2>&1; then
  rm -f "$build_log"
else
  build_status=$?
  cat "$build_log" >&2
  rm -f "$build_log"
  printf '%s\n' \
    'axiom audit: build/currentness gate failed; no axiom audit was run.' >&2
  exit "$build_status"
fi

cache_enabled="${AXIOM_AUDIT_CACHE:-1}"
if [[ "$cache_enabled" != 0 && "$cache_enabled" != 1 ]]; then
  printf '%s\n' \
    "AXIOM_AUDIT_CACHE must be 0 or 1 (received: $cache_enabled)" >&2
  exit 1
fi
# Complete diagnostic inventories cannot be reconstructed from pass counts.
if [[ -n "${AXIOM_AUDIT_REPORT_DIR:-}" ]]; then
  cache_enabled=0
fi
cache_dir="${AXIOM_AUDIT_CACHE_DIR:-$repo_dir/.lake/axiom-audit}"
cache_manifest="$cache_dir/passes-v1.tsv"
if [[ "$cache_enabled" == 1 ]]; then
  mkdir -p "$cache_dir"
fi

cache_schema='ccl-project-axiom-audit-empty-canonical-and-runner-v9'
audit_signature="$({
  printf '%s\n' "$cache_schema" "all_helpers=$all_helpers"
  printf '%s\n' "${all_modules[@]}"
  sed -n '1,$p' "$repo_dir/lean-toolchain"
  sed -n '1,$p' "$repo_dir/scripts/project-module-data.py"
  for reader_part in "$repo_dir"/scripts/lean_module_data/*.py; do
    sed -n '1,$p' "$reader_part"
  done
  sed -n '1,$p' "$repo_dir/scripts/axioms/input_keys.py"
  sed -n '1,$p' "$repo_dir/scripts/axioms/worker_plan.py"
  sed -n '1,$p' "$repo_dir/scripts/verification/environments.py"
  sed -n '1,$p' "$repo_dir/scripts/paths.py"
  sed -n '1,$p' "$repo_dir/scripts/check-axioms.sh"
} | hash_stream)"

available_cpus="$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf '%s\n' 1)"
if [[ ! "$available_cpus" =~ ^[1-9][0-9]*$ ]]; then
  available_cpus=1
fi
default_audit_jobs="$available_cpus"
if (( default_audit_jobs > 2 )); then
  default_audit_jobs=2
fi
requested_audit_jobs="${AXIOM_AUDIT_JOBS:-$default_audit_jobs}"
if [[ ! "$requested_audit_jobs" =~ ^[1-9][0-9]*$ ]]; then
  printf '%s\n' \
    "AXIOM_AUDIT_JOBS must be a positive integer (received: $requested_audit_jobs)" >&2
  exit 1
fi

audit_dir="$(mktemp -d "${TMPDIR:-/tmp}/ccl-project-axioms.XXXXXX")"
declare -a audit_temp_files=()
declare -a audit_logs=()
declare -a audit_pids=()
declare -a audit_worker_indices=()
cache_candidate=''
cleanup() {
  if (( ${#audit_pids[@]} != 0 )); then
    for audit_pid in "${audit_pids[@]}"; do
      if kill -0 "$audit_pid" 2>/dev/null; then
        kill "$audit_pid" 2>/dev/null || true
      fi
    done
  fi
  if [[ -n "$cache_candidate" ]]; then
    rm -f "$cache_candidate"
  fi
  if (( ${#audit_temp_files[@]} != 0 )); then
    rm -f "${audit_temp_files[@]}"
  fi
  rmdir "$audit_dir"
}
trap cleanup EXIT

new_temp_file() {
  local path="$1"
  : > "$path"
  audit_temp_files+=("$path")
}

artifact_fingerprints="$audit_dir/artifact-fingerprints.tsv"
canonical_inputs="$audit_dir/canonical-inputs.tsv"
input_manifest="$audit_dir/input-modules.txt"
input_inventory="$audit_dir/input-modules.json"
metadata_fingerprints="$audit_dir/metadata-fingerprints.tsv"
desired_records="$audit_dir/desired.tsv"
empty_cache="$audit_dir/empty-cache.tsv"
cache_hits="$audit_dir/hits.tsv"
cache_misses="$audit_dir/misses.tsv"
combined_results="$audit_dir/results.tsv"
new_records="$audit_dir/new-records.tsv"
for path in \
    "$artifact_fingerprints" "$canonical_inputs" "$input_manifest" \
    "$input_inventory" "$metadata_fingerprints" \
    "$desired_records" "$empty_cache" \
    "$cache_hits" "$cache_misses" "$combined_results" "$new_records"; do
  new_temp_file "$path"
done

# The generated legacy worker's imports load private bodies throughout each
# root's compiled import closure. An explicit module's ordinary Lake trace follows its
# own import modifiers and need not include those private bodies. Inventory the
# compiled closure with pinned Lean, then hash the actual olean parts and import
# edges before consulting any cached proof result.
printf '%s\n' "${modules[@]}" "${audit_support[@]}" |
  LC_ALL=C sort -u > "$input_manifest"
audit_lean_path="$("$lake_runner" env printenv LEAN_PATH)"
"$lake_runner" env env LEAN_PATH="$audit_lean_path" \
  python3 "$repo_dir/scripts/project-module-data.py" inputs \
    "$input_manifest" "$input_inventory"
PYTHONPATH="$repo_dir${PYTHONPATH:+:$PYTHONPATH}" python3 -m scripts.axioms.input_keys \
  --lean-path "$audit_lean_path" "$input_inventory" > "$metadata_fingerprints"
"$lake_runner" env env LEAN_PATH="$audit_lean_path" \
  python3 "$repo_dir/scripts/project-module-data.py" audit-input-keys \
    "$input_inventory" "$metadata_fingerprints" > "$artifact_fingerprints"
declare -A input_keys=()
while IFS=$'\t' read -r module fingerprint; do
  if [[ ! "$fingerprint" =~ ^[0-9a-f]{64}$ || -n "${input_keys[$module]:-}" ]]; then
    printf 'invalid or duplicate compiled input key: %s\n' "$module" >&2
    exit 1
  fi
  input_keys[$module]="$fingerprint"
done < "$artifact_fingerprints"

for module in "${modules[@]}"; do
  fingerprint="${input_keys[$module]:-}"
  if [[ -z "$fingerprint" ]]; then
    printf 'missing compiled input key for audited module: %s\n' "$module" >&2
    exit 1
  fi
  printf 'project\t%s\t%s\t%s\n' \
    "$module" "$fingerprint" "$audit_signature" >> "$desired_records"
done

# The strict surface has its own dependency-aware key, independent of which
# unrelated project roots were selected. Lake has checked these imports above.
for module in "${audit_support[@]}"; do
  fingerprint="${input_keys[$module]:-}"
  if [[ -z "$fingerprint" ]]; then
    printf 'missing compiled input key for canonical support: %s\n' "$module" >&2
    exit 1
  fi
  printf '%s\t%s\n' "$module" "$fingerprint" >> "$canonical_inputs"
done
canonical_fingerprint="$(hash_stream < "$canonical_inputs")"
printf 'canonical\t@canonical\t%s\t%s\n' \
  "$canonical_fingerprint" "$audit_signature" >> "$desired_records"

cache_source="$empty_cache"
if [[ "$cache_enabled" == 1 && -f "$cache_manifest" ]]; then
  cache_source="$cache_manifest"
fi
awk -F '\t' -v OFS='\t' -v hits="$cache_hits" -v misses="$cache_misses" '
  FILENAME == ARGV[1] {
    if (NF == 5 && $5 ~ /^[0-9]+$/) {
      cached[$1 SUBSEP $2 SUBSEP $3 SUBSEP $4] = $5
    }
    next
  }
  {
    key = $1 SUBSEP $2 SUBSEP $3 SUBSEP $4
    if (key in cached) {
      print $1, $2, $3, $4, cached[key] > hits
    } else {
      print $1, $2, $3, $4 > misses
    }
  }
' "$cache_source" "$desired_records"

miss_count="$(awk 'END {print NR}' "$cache_misses")"
hit_count="$(awk 'END {print NR}' "$cache_hits")"
audit_jobs="$requested_audit_jobs"
if (( miss_count != 0 && audit_jobs > miss_count )); then
  audit_jobs="$miss_count"
fi

declare -a assignment_files=()
declare -a worker_active=()
if (( miss_count != 0 )); then
  # Separate each configured entrypoint import environment and any selected
  # transitive importer. Preserve ordinary dependency clusters and exact misses.
  worker_plan="$audit_dir/worker-plan.tsv"
  new_temp_file "$worker_plan"
  PYTHONPATH="$repo_dir${PYTHONPATH:+:$PYTHONPATH}" python3 -m scripts.axioms.worker_plan \
    --repo "$repo_dir" --jobs "$audit_jobs" \
    "$cache_misses" "$input_inventory" > "$worker_plan"
  worker_count=0
  while IFS=$'\t' read -r worker surface module; do
    if [[ -z "${assignment_files[$worker]:-}" ]]; then
      assignment_file="$audit_dir/assignments.$worker.tsv"
      new_temp_file "$assignment_file"
      assignment_files[worker]="$assignment_file"
      worker_active[worker]=1
      worker_count=$((worker + 1))
    fi
    printf '%s\t%s\n' "$surface" "$module" >> "${assignment_files[$worker]}"
  done < "$worker_plan"
  if (( worker_count == 0 )); then
    printf '%s\n' 'axiom worker plan omitted selected cache misses' >&2
    exit 1
  fi

  for (( worker = 0; worker < worker_count; worker++ )); do
    if [[ "${worker_active[$worker]}" != 1 ]]; then
      continue
    fi
    project_list="$audit_dir/project-modules.$worker.txt"
    audit_source="$audit_dir/ProjectAxiomAudit.$worker.json"
    audit_log="$audit_dir/ProjectAxiomAudit.$worker.log"
    audit_result="$audit_dir/ProjectAxiomAudit.$worker.tsv"
    for path in "$project_list" "$audit_source" "$audit_log" "$audit_result" "$audit_result.closures.jsonl"; do
      new_temp_file "$path"
    done
    if [[ "$report_ir_only" == true ]]; then
      new_temp_file "$audit_result.ir-only.jsonl"
    fi
    audit_logs[worker]="$audit_log"
    awk -F '\t' '$1 == "project" {print $2}' \
      "${assignment_files[$worker]}" > "$project_list"
    audit_canonical=false
    if awk -F '\t' '$1 == "canonical" {found = 1} END {exit !found}' \
        "${assignment_files[$worker]}"; then
      audit_canonical=true
    fi
    # Retain the exact worker invocation as data, without compiling another reader.
    python3 - "$audit_source" "$project_list" "$input_manifest" "$audit_canonical" "$report_ir_only" "$all_helpers" "$audit_result" "${all_modules[@]}" <<'PYWORKER'
import json,sys
from pathlib import Path
output,assigned,inputs,canonical,report_ir_only,all_helpers,result,*project=sys.argv[1:]
Path(output).write_text(json.dumps({'assigned_manifest':assigned,'input_manifest':inputs,
 'canonical':canonical,'report_ir_only':report_ir_only,'all_helpers':all_helpers,'result':result,'project_modules':project,
 'assigned_modules':Path(assigned).read_text().splitlines()},sort_keys=True)+'\n')
PYWORKER

  done

  audit_failed=0
  # Independent environments may outnumber jobs. Only this bounded batch has
  # live Lean processes; every planned worker still runs and reports its roots.
  wait_audit_batch() {
    local index
    for index in "${!audit_pids[@]}"; do
      if ! wait "${audit_pids[$index]}"; then
        audit_failed=1
      fi
    done
    audit_pids=()
  }
  for (( worker = 0; worker < worker_count; worker++ )); do
    project_boundary="$audit_dir/all-project-modules.txt"
    if [[ ! -f "$project_boundary" ]]; then
      new_temp_file "$project_boundary"
      printf '%s\n' "${all_modules[@]}" > "$project_boundary"
    fi
    audit_canonical=false
    if awk -F '\t' '$1 == "canonical" {found = 1} END {exit !found}' "${assignment_files[$worker]}"; then audit_canonical=true; fi
    report_options=()
    if [[ "$report_ir_only" == true ]]; then report_options+=(--report-ir-only); fi
    if [[ "$all_helpers" == true ]]; then report_options+=(--all-helpers); fi
    "$lake_runner" env env LEAN_PATH="$audit_lean_path" \
      python3 "$repo_dir/scripts/project-module-data.py" audit \
      --project "$project_boundary" --assigned "$audit_dir/project-modules.$worker.txt" \
      --canonical "$audit_canonical" --result "$audit_dir/ProjectAxiomAudit.$worker.tsv" \
      "${report_options[@]}" >"${audit_logs[$worker]}" 2>&1 &
    audit_pids+=("$!")
    audit_worker_indices+=("$worker")
    if (( ${#audit_pids[@]} >= audit_jobs )); then
      wait_audit_batch
    fi
  done
  wait_audit_batch
  for worker in "${audit_worker_indices[@]}"; do
    sed -n '1,$p' "${audit_logs[$worker]}"
  done
  if [[ -n "${AXIOM_AUDIT_REPORT_DIR:-}" ]]; then
    mkdir -p "$AXIOM_AUDIT_REPORT_DIR"
    report_directory="$(mktemp -d "$AXIOM_AUDIT_REPORT_DIR/run.XXXXXX")"
    cp "$desired_records" "$report_directory/inputs.tsv"
    cp "$input_inventory" "$report_directory/module-inputs.json"
    cp "$metadata_fingerprints" "$report_directory/metadata-fingerprints.tsv"
    cp "$artifact_fingerprints" "$report_directory/host-input-fingerprints.tsv"
    cp "$worker_plan" "$report_directory/worker-plan.tsv"
    cp "$repo_dir/scripts/lean_module_data/audit.py" "$report_directory/checker.py.txt"
    cp "$repo_dir/scripts/lean_module_data/audit_metadata.py" "$report_directory/root-metadata.py.txt"
    for worker in "${audit_worker_indices[@]}"; do
      cp "$audit_dir/ProjectAxiomAudit.$worker.tsv.closures.jsonl" \
        "$report_directory/closures.$worker.jsonl"
      cp "$audit_dir/ProjectAxiomAudit.$worker.json" "$report_directory/worker.$worker.json"
      if [[ "$report_ir_only" == true ]]; then
        cp "$audit_dir/ProjectAxiomAudit.$worker.tsv.ir-only.jsonl" "$report_directory/ir-only.$worker.jsonl"
      fi
      cp "${assignment_files[$worker]}" "$report_directory/assignments.$worker.tsv"
    done
    printf 'axiom audit diagnostic records: %s\n' "$report_directory"
  fi
  if (( audit_failed != 0 )); then
    exit 1
  fi
  for worker in "${audit_worker_indices[@]}"; do
    sed -n '1,$p' "$audit_dir/ProjectAxiomAudit.$worker.tsv" >> "$combined_results"
  done
fi

# Attach each fresh declaration count to the exact desired artifact key and
# reject missing, duplicate, malformed, or unsolicited worker results.
awk -F '\t' -v OFS='\t' '
  FILENAME == ARGV[1] {
    key = $1 SUBSEP $2
    if (NF != 3 || $3 !~ /^[0-9]+$/ || key in counts) {
      bad = 1
    } else {
      counts[key] = $3
    }
    next
  }
  {
    key = $1 SUBSEP $2
    expected[key] = 1
    if (!(key in counts)) {
      bad = 1
    } else {
      print $1, $2, $3, $4, counts[key]
    }
  }
  END {
    for (key in counts) {
      if (!(key in expected)) bad = 1
    }
    if (bad) {
      print "axiom audit worker returned inconsistent cache results" > "/dev/stderr"
      exit 1
    }
  }
' "$combined_results" "$cache_misses" > "$new_records"

if [[ "$cache_enabled" == 1 ]]; then
  cache_candidate="$(mktemp "$cache_dir/passes-v1.tsv.XXXXXX")"
else
  cache_candidate="$audit_dir/cache-candidate.tsv"
  new_temp_file "$cache_candidate"
fi
LC_ALL=C sort -u "$cache_hits" "$new_records" > "$cache_candidate"

summary="$(awk -F '\t' -v expected="${#modules[@]}" '
  $1 == "project" {projectRecords += 1; projectDeclarations += $5}
  $1 == "canonical" {canonicalRecords += 1; canonicalDeclarations += $5}
  END {
    if (projectRecords != expected ||
        canonicalRecords != 1 || canonicalDeclarations == 0) {
      exit 1
    }
    print projectDeclarations, canonicalDeclarations
  }
' "$cache_candidate")" || {
  printf '%s\n' "axiom audit cache did not cover the complete audit surface" >&2
  exit 1
}
read -r project_declarations canonical_declarations <<< "$summary"

if [[ "$cache_enabled" == 1 ]]; then
  # A scoped pass must not discard successful results for unselected roots.
  # Summary validation above covers only this invocation, not retained records.
  retained_records="$audit_dir/retained.tsv"
  new_temp_file "$retained_records"
  if [[ -f "$cache_manifest" ]]; then
    awk -F '\t' '
      FILENAME == ARGV[1] {selected[$1 SUBSEP $2] = 1; next}
      NF == 5 && !(($1 SUBSEP $2) in selected) {print}
    ' "$desired_records" "$cache_manifest" > "$retained_records"
  fi
  cat "$retained_records" >> "$cache_candidate"
  mv "$cache_candidate" "$cache_manifest"
  cache_candidate=''
fi

printf 'axiom audit cache: %s hits, %s checked; ' "$hit_count" "$miss_count"
printf 'audited %s project declarations and %s strict canonical declarations; ' \
  "$project_declarations" "$canonical_declarations"
printf '%s\n' 'allowed axioms: []'

# The strict canonical axiom scan ran above in a repository worker.  Execute
# the linked regression so imported private code and its compiled instances
# are available to the runtime.
"$repo_dir/.lake/build/bin/fraction_regression"
