#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
lake_runner="$repo_dir/scripts/run-lake.sh"
identifier_pattern="^[A-Za-z_][A-Za-z0-9_?']*(\\.[A-Za-z_][A-Za-z0-9_?']*)*$"

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

trace_dir="$(mktemp -d "${TMPDIR:-/tmp}/ccl-axiom-trace.XXXXXX")"
trace_source="$trace_dir/AxiomTraceRun.lean"
cleanup() {
  rm -f "$trace_source"
  rmdir "$trace_dir"
}
trap cleanup EXIT

{
  printf '%s\n' 'import Lean.Util.CollectAxioms'
  printf '%s\n' 'import Lean.Util.FoldConsts'
  printf '%s\n' 'import Lean.Elab.Command'
  printf 'import %s\n' "$module"
  sed '/^import /d' "$repo_dir/scripts/AxiomTrace.lean"
  printf '\n'
  for declaration in "$@"; do
    if [[ $mode == "use" ]]; then
      printf '#trace_use %s in %s\n' "$target" "$declaration"
    else
      printf '#trace_axiom %s in %s\n' "$target" "$declaration"
    fi
  done
} > "$trace_source"

"$lake_runner" lean "$trace_source"
