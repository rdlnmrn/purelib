#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

cd "$repo_root/papers/RFAP"
tectonic RFAP.tex
tectonic RFAP-2.tex
cd "$repo_root/papers/CCL"
tectonic CCL-1.tex
tectonic CCL-2.tex
