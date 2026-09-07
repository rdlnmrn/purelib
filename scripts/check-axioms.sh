#!/usr/bin/env bash
set -euo pipefail

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
while IFS= read -r source; do
  relative="${source#"$repo_dir/"}"
  module="${relative%.lean}"
  modules+=("${module//\//.}")
done < <(
  find "$repo_dir" \
    \( -path "$repo_dir/.git" \
      -o -path "$repo_dir/.lake" \
      -o -path "$repo_dir/.elan" \
      -o -path "$repo_dir/.external" \
      -o -path "$repo_dir/legacy" \
      -o -path "$repo_dir/scripts" \
      -o -path "$repo_dir/mathlib/RFAP/LegacyQuotientFraction.lean" \) \
    -prune -o -type f -name '*.lean' -print | sort -u
)

if (( ${#modules[@]} == 0 )); then
  printf '%s\n' "project axiom audit found no Lean modules" >&2
  exit 1
fi

# The build remains mandatory.  In addition to checking warnings, it makes
# Lake's content hashes authoritative for the compiled module data audited
# below.  Every active module is named because the default facades do not
# necessarily re-export every internal project module.
"$lake_runner" --wfail build "${modules[@]}" >/dev/null

cache_enabled="${AXIOM_AUDIT_CACHE:-1}"
if [[ "$cache_enabled" != 0 && "$cache_enabled" != 1 ]]; then
  printf '%s\n' \
    "AXIOM_AUDIT_CACHE must be 0 or 1 (received: $cache_enabled)" >&2
  exit 1
fi
cache_dir="${AXIOM_AUDIT_CACHE_DIR:-$repo_dir/.lake/axiom-audit}"
cache_manifest="$cache_dir/passes-v1.tsv"
if [[ "$cache_enabled" == 1 ]]; then
  mkdir -p "$cache_dir"
fi

cache_schema='ccl-project-axiom-audit-v1'
audit_signature="$({
  printf '%s\n' "$cache_schema"
  sed -n '1,$p' "$repo_dir/lean-toolchain"
  sed -n '1,$p' "$repo_dir/scripts/ProjectAxiomAudit.lean"
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
audit_object_overlay=''
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
  if [[ -n "$audit_object_overlay" ]]; then
    rm -rf -- "$audit_object_overlay"
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
      printf 'axiom-audit object overlay collision at %s\n' "$target" >&2
      return 1
    fi
    ln -s "$source_path" "$target"
  done < <(find "$source_root" \( -type f -o -type l \) -print)
}

artifact_fingerprints="$audit_dir/artifact-fingerprints.tsv"
desired_records="$audit_dir/desired.tsv"
empty_cache="$audit_dir/empty-cache.tsv"
cache_hits="$audit_dir/hits.tsv"
cache_misses="$audit_dir/misses.tsv"
combined_results="$audit_dir/results.tsv"
new_records="$audit_dir/new-records.tsv"
for path in \
    "$artifact_fingerprints" "$desired_records" "$empty_cache" \
    "$cache_hits" "$cache_misses" "$combined_results" "$new_records"; do
  new_temp_file "$path"
done

for module in "${modules[@]}"; do
  module_path="${module//.//}"
  hash_file="$repo_dir/.lake/build/lib/lean/$module_path.olean.hash"
  if [[ ! -f "$hash_file" ]]; then
    printf '%s\n' "missing Lake olean hash for audited module: $module" >&2
    exit 1
  fi
  olean_hash="$(sed -n '1p' "$hash_file")"
  if [[ ! "$olean_hash" =~ ^[0-9a-fA-F]{16}$ ]]; then
    printf '%s\n' "invalid Lake olean hash for audited module: $module" >&2
    exit 1
  fi
  printf '%s\t%s\n' "$module" "$olean_hash" >> "$artifact_fingerprints"
  printf 'project\t%s\t%s\t%s\n' \
    "$module" "$olean_hash" "$audit_signature" >> "$desired_records"
done

# The focused canonical scan is one aggregate cache surface.  Fingerprinting
# every active project artifact deliberately over-invalidates it: this avoids
# duplicating its module list in the shell while ensuring that any compiled
# project change rechecks the strict surface in an already-needed worker.
project_fingerprint="$(hash_stream < "$artifact_fingerprints")"
printf 'canonical\t@canonical\t%s\t%s\n' \
  "$project_fingerprint" "$audit_signature" >> "$desired_records"

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
  # On a case-insensitive filesystem, upstream `Mathlib/` and the project's
  # lowercase `mathlib/` occupy the same lookup spelling.  Neither ordinary
  # LEAN_PATH order can expose both trees: whichever comes first hides the
  # other.  Merge symlinks to both already-built object trees in a temporary
  # prefix, as the independent nanoda exporter does.
  lake_lean_path="$("$lake_runner" env printenv LEAN_PATH)"
  project_objects="$repo_dir/.lake/build/lib/lean"
  mathlib_objects="$repo_dir/.lake/packages/mathlib/.lake/build/lib/lean"
  audit_object_overlay="$audit_dir/object-overlay"
  mkdir -p "$audit_object_overlay"
  link_object_tree "$project_objects/mathlib" "$audit_object_overlay/mathlib"
  link_object_tree "$mathlib_objects/Mathlib" "$audit_object_overlay/Mathlib"
  audit_lean_path="$audit_object_overlay:$lake_lean_path"

  for (( worker = 0; worker < audit_jobs; worker++ )); do
    assignment_file="$audit_dir/assignments.$worker.tsv"
    new_temp_file "$assignment_file"
    assignment_files[worker]="$assignment_file"
    worker_active[worker]=0
  done

  assignment_index=0
  while IFS=$'\t' read -r surface module _hash _signature; do
    if (( audit_jobs == 1 )); then
      worker=0
    elif [[ "$surface" == canonical ]]; then
      # Keep the strict canonical scan with the non-DivineProportions shard.
      worker=1
    elif (( audit_jobs == 2 )); then
      if [[ "$module" == DivineProportions || "$module" == DivineProportions.* ]]; then
        worker=0
      else
        worker=1
      fi
    else
      # Preserve large dependency clusters for explicit higher job counts.
      case "$module" in
        DivineProportions|DivineProportions.*) worker=0 ;;
        CCL|CCL.*|RFAP|RFAP.*|mathlib|mathlib.*) worker=$((1 % audit_jobs)) ;;
        FiniteMeasure|FiniteMeasure.*|RationalRotations|RationalRotations.*)
          worker=$((2 % audit_jobs)) ;;
        *) worker=$((assignment_index % audit_jobs)) ;;
      esac
    fi
    printf '%s\t%s\n' "$surface" "$module" >> "${assignment_files[$worker]}"
    worker_active[worker]=1
    assignment_index=$((assignment_index + 1))
  done < "$cache_misses"

  for (( worker = 0; worker < audit_jobs; worker++ )); do
    if [[ "${worker_active[$worker]}" != 1 ]]; then
      continue
    fi
    project_list="$audit_dir/project-modules.$worker.txt"
    audit_source="$audit_dir/ProjectAxiomAudit.$worker.lean"
    audit_log="$audit_dir/ProjectAxiomAudit.$worker.log"
    audit_result="$audit_dir/ProjectAxiomAudit.$worker.tsv"
    for path in "$project_list" "$audit_source" "$audit_log" "$audit_result"; do
      new_temp_file "$path"
    done
    audit_logs[worker]="$audit_log"
    awk -F '\t' '$1 == "project" {print $2}' \
      "${assignment_files[$worker]}" > "$project_list"
    audit_canonical=false
    if awk -F '\t' '$1 == "canonical" {found = 1} END {exit !found}' \
        "${assignment_files[$worker]}"; then
      audit_canonical=true
    fi
    escaped_result="${audit_result//\\/\\\\}"
    escaped_result="${escaped_result//\"/\\\"}"
    {
      while IFS= read -r module; do
        printf 'import %s\n' "$module"
      done < "$project_list"
      printf '\n'
      sed -n '1,$p' "$repo_dir/scripts/ProjectAxiomAudit.lean"
      printf '%s\n' '' '#audit_project_axioms project_modules ['
      for (( index = 0; index < ${#modules[@]}; index++ )); do
        if (( index + 1 == ${#modules[@]} )); then
          printf '  %s\n' "${modules[$index]}"
        else
          printf '  %s,\n' "${modules[$index]}"
        fi
      done
      printf '%s\n' '] audited_modules ['
      project_index=0
      project_count="$(awk 'END {print NR}' "$project_list")"
      while IFS= read -r module; do
        project_index=$((project_index + 1))
        if (( project_index == project_count )); then
          printf '  %s\n' "$module"
        else
          printf '  %s,\n' "$module"
        fi
      done < "$project_list"
      printf '] audit_canonical %s results "%s"\n' \
        "$audit_canonical" "$escaped_result"
    } > "$audit_source"
  done

  for (( worker = 0; worker < audit_jobs; worker++ )); do
    if [[ "${worker_active[$worker]}" != 1 ]]; then
      continue
    fi
    "$lake_runner" env env LEAN_PATH="$audit_lean_path" \
      lean -E warning "$audit_dir/ProjectAxiomAudit.$worker.lean" \
        >"${audit_logs[$worker]}" 2>&1 &
    audit_pids+=("$!")
    audit_worker_indices+=("$worker")
  done

  audit_failed=0
  for index in "${!audit_pids[@]}"; do
    if ! wait "${audit_pids[$index]}"; then
      audit_failed=1
    fi
  done
  audit_pids=()
  for worker in "${audit_worker_indices[@]}"; do
    sed -n '1,$p' "${audit_logs[$worker]}"
  done
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
    if (projectRecords != expected || projectDeclarations == 0 ||
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
  mv "$cache_candidate" "$cache_manifest"
  cache_candidate=''
fi

printf 'axiom audit cache: %s hits, %s checked; ' "$hit_count" "$miss_count"
printf 'audited %s project declarations and %s strict canonical declarations; ' \
  "$project_declarations" "$canonical_declarations"
printf '%s\n' 'allowed axioms: [propext]'

# The strict canonical axiom scan ran above in a repository worker.  Keep the
# executable regression, but do not start a redundant Lean audit process.
"$lake_runner" --wfail build scripts.CanonicalFractionRegressionMain >/dev/null
"$lake_runner" env lean \
  --setup "$repo_dir/.lake/build/ir/scripts/CanonicalFractionRegressionMain.setup.json" \
  --run "$repo_dir/scripts/CanonicalFractionRegressionMain.lean"
