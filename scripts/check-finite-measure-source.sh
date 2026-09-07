#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source_roots=(
  "$repo_dir/FiniteMeasure"
  "$repo_dir/FiniteMeasure.lean"
  "$repo_dir/RFAP/Measure"
  "$repo_dir/CCL/Measure"
)

forbidden='\b(noncomputable|classical|native_decide|sorry|admit|maxRecDepth|maxHeartbeats)\b|Classical\.'
if rg -n "$forbidden" "${source_roots[@]}"; then
  printf '%s\n' "forbidden nonconstructive or resource-setting source found" >&2
  exit 1
fi

broad_import='^import .*(MeasureTheory|Topology|SetTheory|Cardinal|Analysis)'
if rg -n "$broad_import" "${source_roots[@]}"; then
  printf '%s\n' "broad or completed-object import found in finite measure source" >&2
  exit 1
fi

if rg -n '^import CCL\.|CCL\.' "$repo_dir/RFAP/Measure"; then
  printf '%s\n' "Paper-I RFAP measure source crosses into CCL" >&2
  exit 1
fi

printf '%s\n' "finite-measure source audit passed"
