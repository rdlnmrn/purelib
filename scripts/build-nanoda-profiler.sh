#!/usr/bin/env bash
# Link a diagnostic driver to the existing pinned library, without rebuilding it.
set -euo pipefail
root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
source="$root/scripts/profiling/Nanoda.rs"
release="$root/.external/nanoda/target/release"
[[ -s "$release/libnanoda_lib.rlib" ]] || { printf 'missing built nanoda library\n' >&2; exit 1; }
key=$(
  {
    printf '%s\n' 'nanoda-profile-v1 opt-level=3 overflow-checks=yes lto warnings=error'
    rustc --version
    sha256sum "$(command -v rustc)"
    sha256sum "$root/scripts/build-nanoda-profiler.sh" "$source" "$release/libnanoda_lib.rlib" "$release"/deps/*.rlib
  } | sha256sum | cut -d ' ' -f 1
)
cache="$root/.lake/nanoda-profile-tools/$key"
mkdir -p "$cache"
exec 9>"$cache/build.lock"
flock 9
binary="$cache/profiler"
if [[ -s "$binary" && -s "$binary.sha256" ]] &&
   [[ "$(sha256sum "$binary" | cut -d ' ' -f 1)" == "$(cat "$binary.sha256")" ]]; then
  printf '%s\n' "$binary"
  exit 0
fi
pending=$(mktemp -d "$cache/build.XXXXXX")
trap 'rm -rf -- "$pending"' EXIT
rustc -D warnings --edition=2021 --crate-name nanoda_profile -C opt-level=3 -C overflow-checks=yes -C lto \
  --extern "nanoda_lib=$release/libnanoda_lib.rlib" -L "dependency=$release/deps" \
  "$source" -o "$pending/profiler" >&2
sha256sum "$pending/profiler" | cut -d ' ' -f 1 > "$pending/profiler.sha256"
mv -- "$pending/profiler" "$binary"
mv -- "$pending/profiler.sha256" "$binary.sha256"
printf '%s\n' "$binary"
