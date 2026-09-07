#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

cd "$repo_root"
tectonic RFAP.tex
tectonic RFAP-2.tex
tectonic CCL-1.tex
tectonic CCL-2.tex
