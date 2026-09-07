#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lake_runner="$repo_dir/scripts/run-lake.sh"

"$lake_runner" build ImportGraph.Imports.FromSource >/dev/null

report="$({
  cd "$repo_dir"
  "$lake_runner" env lean "$repo_dir/scripts/PaperIIImports.lean"
})"

printf '%s\n' "$report"

missing_facade=''
for required in CCL.Paper CCL.Bridge.Paper RFAP.Paper; do
  if ! grep -qx "$required" <<< "$report"; then
    missing_facade+="$required"$'\n'
  fi
done

unexpected_legacy="$(printf '%s\n' "$report" | \
  grep -E '(^|\.)(Legacy|FTA)(\.|$)' || true)"
source_legacy="$(rg -n '(^import (legacy|FTA)\.|\b(legacy|FTA)\.)' \
  "$repo_dir/CCL" "$repo_dir/CCL.lean" -g '*.lean' || true)"
stale_names="$(rg -n 'CCL[./]Constructive' \
  "$repo_dir/CCL" "$repo_dir/CCL.lean" -g '*.lean' || true)"

if [[ -n "$missing_facade$unexpected_legacy$source_legacy$stale_names" ]]; then
  printf '%s\n' "Combined CCL-1/CCL-2 import boundary is inconsistent:" >&2
  [[ -z "$missing_facade" ]] || \
    printf 'missing required imports:\n%s' "$missing_facade" >&2
  [[ -z "$unexpected_legacy" ]] || \
    printf 'legacy modules in closure:\n%s\n' "$unexpected_legacy" >&2
  [[ -z "$source_legacy" ]] || \
    printf 'legacy references in CCL sources:\n%s\n' "$source_legacy" >&2
  [[ -z "$stale_names" ]] || \
    printf 'stale CCL module names:\n%s\n' "$stale_names" >&2
  exit 1
fi
