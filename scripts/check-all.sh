#!/usr/bin/env bash
set -euo pipefail
repo_dir="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
export PYTHONPATH="$repo_dir${PYTHONPATH:+:$PYTHONPATH}"
exec python3 -m scripts.verification.completion "$@"
