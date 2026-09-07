#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

if [[ -n "${ELAN_HOME:-}" && -x "$ELAN_HOME/bin/lake" ]]; then
  exec env ELAN_NO_UPDATE_CHECK=1 "$ELAN_HOME/bin/lake" "$@"
fi

local_elan_home="$repo_root/.elan"
if [[ -x "$local_elan_home/bin/lake" ]]; then
  exec env ELAN_NO_UPDATE_CHECK=1 ELAN_HOME="$local_elan_home" \
    "$local_elan_home/bin/lake" "$@"
fi

if lake_bin=$(command -v lake); then
  exec env ELAN_NO_UPDATE_CHECK=1 "$lake_bin" "$@"
fi

printf '%s\n' \
  "missing Lake executable: install the toolchain pinned by lean-toolchain" >&2
exit 1
