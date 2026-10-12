#!/usr/bin/env bash
set -euo pipefail
repo_dir="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
# Preserve user-relative arguments while making the ordinary package importable.
export PYTHONPATH="$repo_dir${PYTHONPATH:+:$PYTHONPATH}"
exec python3 -m scripts.verification.source_policy "$@"
