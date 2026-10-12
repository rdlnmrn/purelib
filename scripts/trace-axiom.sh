#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
# Lean prints private declaration names with a numeric private-prefix part.
identifier_pattern="^[A-Za-z_][A-Za-z0-9_?']*(\\.([A-Za-z_][A-Za-z0-9_?']*|[0-9]+))*$"

target="Quot.sound"
mode="axiom"
if [[ ${1:-} == "--use" ]]; then
  if (( $# < 4 )); then
    printf '%s\n' \
      "usage: $0 --use DECLARATION MODULE CONTAINER [CONTAINER ...]" >&2
    exit 2
  fi
  mode="use"
  target="$2"
  shift 2
elif [[ ${1:-} == "--axiom" ]]; then
  if (( $# < 4 )); then
    printf '%s\n' \
      "usage: $0 [--axiom AXIOM] MODULE DECLARATION [DECLARATION ...]" >&2
    exit 2
  fi
  target="$2"
  shift 2
fi

if (( $# < 2 )); then
  printf '%s\n' \
    "usage: $0 [--axiom AXIOM] MODULE DECLARATION [DECLARATION ...]" >&2
  exit 2
fi

module="$1"
shift

for identifier in "$target" "$module" "$@"; do
  if [[ ! $identifier =~ $identifier_pattern ]]; then
    printf 'invalid Lean identifier: %s\n' "$identifier" >&2
    exit 2
  fi
done

# The pinned host reader inspects compiled metadata; no target code executes.
exec "$repo_dir/scripts/run-lake.sh" env python3 "$repo_dir/scripts/project-module-data.py" trace \
  --mode "$mode" --target "$target" "$module" "$@"
