#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
"$repo_dir/scripts/run-lake.sh" env lean -E warning \
  "$repo_dir/scripts/CanonicalFractionAxiomAudit.lean"
"$repo_dir/scripts/run-lake.sh" --wfail build \
  scripts.CanonicalFractionRegressionMain >/dev/null
"$repo_dir/scripts/run-lake.sh" env lean \
  --setup "$repo_dir/.lake/build/ir/scripts/CanonicalFractionRegressionMain.setup.json" \
  --run "$repo_dir/scripts/CanonicalFractionRegressionMain.lean"
