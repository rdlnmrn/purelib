#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lake_runner="$repo_dir/scripts/run-lake.sh"

"$lake_runner" build ImportGraph.Imports.FromSource >/dev/null

report="$({
  cd "$repo_dir"
  "$lake_runner" lean "$repo_dir/scripts/PaperIImports.lean"
})"

printf '%s\n' "$report"

unexpected_ccl="$(printf '%s\n' "$report" | grep '^CCL\.' || true)"
unexpected_rfap="$(printf '%s\n' "$report" | \
  grep -E '^RFAP\..*CCL' || true)"
rfap_source_ccl="$(rg -n '(^import CCL\.|\bCCL\.)' \
  "$repo_dir/RFAP" "$repo_dir/RFAP.lean" -g '*.lean' || true)"
rfap_named_ccl="$(rg --files "$repo_dir/RFAP" -g '*CCL*.lean' || true)"

if [[ -n "$unexpected_ccl$unexpected_rfap$rfap_source_ccl$rfap_named_ccl" ]]; then
  printf '%s\n' "RFAP boundary contains CCL modules or references:" >&2
  printf '%s\n%s\n%s\n%s\n' \
    "$unexpected_ccl" "$unexpected_rfap" \
    "$rfap_source_ccl" "$rfap_named_ccl" >&2
  exit 1
fi
