#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
export PYTHONPATH="$repo_root${PYTHONPATH:+:$PYTHONPATH}"

if [[ "${CCL_BUILD_PROFILE_DRIVER:-}" != 1 ]]; then
  exec python3 -m scripts.profiling.build "$@"
fi
unset CCL_BUILD_PROFILE_DRIVER

# Keep explicit scopes; an unscoped lint command checks every active source.
args_file=$(mktemp "${TMPDIR:-/tmp}/ccl-lake-args.XXXXXX")
trap 'rm -f "$args_file"' EXIT
python3 -m scripts.linting.lake_args "$@" > "$args_file"
mapfile -d '' -t lake_args < "$args_file"
rm -f "$args_file"
trap - EXIT

# Lake 4.32.2 can race when several cold plugin facets build the same native
# dependency. Prepare the reviewed providers in order, retaining Lake's caches.
run_lake() {
  local lake_executable="$1"
  shift
  export ELAN_NO_UPDATE_CHECK=1
  python3 -m scripts.linting.providers "$lake_executable" "$@"
  exec python3 -m scripts.linting.runner "$lake_executable" "$@"
}

# The patched Core prefix has its own sources, four-part artifacts and native compiler.
# Lake's collocated-toolchain detection otherwise ignores LEAN_SYSROOT.
core_prefix="${CCL_CORE_PREFIX:-$repo_root/.lake/core-toolchain}"
if [[ -f "$repo_root/scripts/toolchain/config.json" ]]; then
  if [[ ! -f "$core_prefix/CORE-PREFIX.json" ]]; then
    upstream_lean=$(env ELAN_NO_UPDATE_CHECK=1 elan which lean)
    upstream_base=$(CDPATH= cd -- "$(dirname -- "$upstream_lean")/.." && pwd)
    python3 -m scripts.toolchain.rebuild_prefix \
      --base "$upstream_base" --config "$repo_root/scripts/toolchain/config.json" \
      --prefix "$core_prefix" --cache "$repo_root/.lake/core-toolchain-build" \
      --repo "$repo_root"
  fi
  core_key=$(python3 -m scripts.toolchain.prepare_prefix check \
    --config "$repo_root/scripts/toolchain/config.json" --prefix "$core_prefix")
  export LEAN_SYSROOT="$core_prefix" LAKE_OVERRIDE_LEAN=true LEAN_GITHASH="$core_key"
  export PATH="$core_prefix/bin:$PATH"
  patched_lake=$(python3 -m scripts.toolchain.prepare_lake \
    --prefix "$core_prefix" --cache "$repo_root/.lake/lake-toolchain")
  export PATH="${patched_lake%/*}:$PATH"
  run_lake "$patched_lake" "${lake_args[@]}"
fi

if [[ -n "${ELAN_HOME:-}" && -x "$ELAN_HOME/bin/lake" ]]; then
  run_lake "$ELAN_HOME/bin/lake" "${lake_args[@]}"
fi

local_elan_home="$repo_root/.elan"
if [[ -x "$local_elan_home/bin/lake" ]]; then
  export ELAN_HOME="$local_elan_home"
  run_lake "$local_elan_home/bin/lake" "${lake_args[@]}"
fi

if lake_bin=$(command -v lake); then
  run_lake "$lake_bin" "${lake_args[@]}"
fi

printf '%s\n' \
  "missing Lake executable: install the toolchain pinned by lean-toolchain" >&2
exit 1
