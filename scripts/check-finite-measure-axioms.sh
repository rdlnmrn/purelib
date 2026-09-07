#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

"$repo_dir/scripts/check-finite-measure-source.sh"
"$repo_dir/scripts/check-finite-measure-imports.sh" >/dev/null

exec "$repo_dir/scripts/check-axioms.sh"
