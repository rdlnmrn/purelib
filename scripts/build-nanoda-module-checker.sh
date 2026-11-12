#!/usr/bin/env bash
# Link module scheduling to the unchanged pinned independent kernel library.
set -euo pipefail
root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
source="$root/scripts/nanoda/Modules.rs"
release="$root/.external/nanoda/target/release"
rustc=${RUSTC:-rustc}
if ! command -v "$rustc" >/dev/null 2>&1 && [[ -x "${CARGO_HOME:-$HOME/.cargo}/bin/rustc" ]]; then
  rustc="${CARGO_HOME:-$HOME/.cargo}/bin/rustc"
fi
[[ -s "$release/libnanoda_lib.rlib" ]] || { printf 'missing built nanoda library\n' >&2; exit 1; }
key=$(
  {
    printf '%s\n' 'nanoda-modules-v1 opt-level=3 overflow-checks=yes lto warnings=error'
    "$rustc" --version
    sha256sum "$(command -v "$rustc")" "$0" "$source" "$release/libnanoda_lib.rlib" "$release"/deps/*.rlib
  } | sha256sum | cut -d ' ' -f 1
)
cache="$root/.lake/nanoda-module-tools/$key"
mkdir -p "$cache"
exec 9>"$cache/build.lock"
flock 9
binary="$cache/checker"
if [[ -s "$binary" && -s "$binary.sha256" ]] &&
   [[ "$(sha256sum "$binary" | cut -d ' ' -f 1)" == "$(cat "$binary.sha256")" ]]; then
  printf '%s\n' "$binary"
  exit 0
fi
pending=$(mktemp -d "$cache/build.XXXXXX")
trap 'rm -rf -- "$pending"' EXIT
timeout --signal=TERM --kill-after=15s 300s \
  "$rustc" -D warnings --edition=2021 --crate-name nanoda_modules \
  -C opt-level=3 -C overflow-checks=yes -C lto \
  --extern "nanoda_lib=$release/libnanoda_lib.rlib" -L "dependency=$release/deps" \
  "$source" -o "$pending/checker" >&2
sha256sum "$pending/checker" | cut -d ' ' -f 1 > "$pending/checker.sha256"
mv -- "$pending/checker" "$binary"
mv -- "$pending/checker.sha256" "$binary.sha256"
printf '%s\n' "$binary"
