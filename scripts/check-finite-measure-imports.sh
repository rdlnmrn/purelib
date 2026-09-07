#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lake_runner="$repo_dir/scripts/run-lake.sh"

"$lake_runner" build ImportGraph.Imports.FromSource >/dev/null

report="$({
  cd "$repo_dir"
  "$lake_runner" lean "$repo_dir/scripts/FiniteMeasureImports.lean"
})"

printf '%s\n' "$report"

# This is intentionally a narrow allowlist.  New upstream modules must be
# examined and added explicitly, rather than entering the closure through a
# broad convenience import.
allowed='^(FiniteMeasure\.|RFAP\.|CCL\.|mathlib\.RFAP\.|mathlib\.CCL\.Integral$|mathlib\.Data\.Constructive(Fin|List)$|mathlib\.Tactic\.QuotientFree(Omega|Ring)$|Init\.Data\.Fin\.Lemmas$|Init\.Data\.List\.(Attach|Find|OfFn)$|Init\.Data\.List\.Nat\.(Pairwise|Range)$|Lean\.Elab\.Tactic\.Omega$|Mathlib\.Algebra\.Field\.MinimalAxioms$|Mathlib\.Algebra\.Order\.Ring\.Defs$|Mathlib\.Algebra\.Ring\.(Defs|MinimalAxioms)$|Mathlib\.Data\.List\.Basic$|Mathlib\.Tactic\.NormNum\.Pow$|Mathlib\.Tactic\.Ring\.Basic$)'
unexpected="$(printf '%s\n' "$report" | grep -Ev "$allowed" || true)"

if [[ -n "$unexpected" ]]; then
  printf '%s\n' "unaudited module in finite-measure transitive import closure:" >&2
  printf '%s\n' "$unexpected" >&2
  exit 1
fi

printf '%s\n' "finite-measure transitive import audit passed"
