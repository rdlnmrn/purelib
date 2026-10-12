#!/usr/bin/env bash
set -euo pipefail

# Focused regression for compiler-induced owner replay.  No generated banks,
# root isolation, runtime observations, or increased Lean limits are needed.
check_models=0
if [[ $# == 1 && $1 == --models ]]; then
  check_models=1
elif [[ $# != 0 ]]; then
  printf 'usage: check-prepared-projections.sh [--models]\n' >&2
  exit 1
fi
repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
# Require current owner artifacts from the warning-fatal project build.
# Fresh consumer emission and C compilation below are independent of Lake's
# transitive export-info jobs.
scripts/run-lake.sh --wfail --no-build build Purelib.Riemann.Branches.PreparedSheetContinuation:c

projection_tmp=$(mktemp -d /tmp/ccl-prepared-projections.XXXXXX)
cleanup() {
  rm -rf -- "$projection_tmp"
}
trap cleanup EXIT

# Compile the selected complete C files directly.
scripts/run-lake.sh env leanc -DLEAN_EXPORTING -c \
  .lake/build/ir/Purelib/Riemann/Branches/PreparedSheetContinuation.c \
  -o "$projection_tmp/Owner.o"

scripts/run-lake.sh env lean -DwarningAsError=true \
  -o "$projection_tmp/Projection.olean" -c "$projection_tmp/Projection.c" \
  Test/Riemann/Prepared/SubdivisionProjections.lean

# Each public consumer must select the exposed original stored-data
# implementation, preserving its declaration identity.
for projection in endpoint terminalOwner stepCount parameterEdges preparedBoxes requests toClearPath; do
  if ! rg -q "_Subdivision_${projection}Stored___redArg\\(" "$projection_tmp/Projection.c"; then
    printf 'missing direct stored-data implementation for %s\n' "$projection" >&2
    exit 1
  fi
done
if rg -n '_PreparedSheetContinuation_(advance|advanceCached|prepared|recentered)___' \
    "$projection_tmp/Projection.c"; then
  printf 'a public projection consumer replays owner preparation\n' >&2
  exit 1
fi

# Inspect the selected implementations as well, not just their callers.
awk '
  /^LEAN_EXPORT.*\{/ {
    selected = ($0 ~ /_Subdivision_(endpoint|terminalOwner|stepCount|parameterEdges|preparedBoxes|requests|toClearPath)Stored___redArg\(/)
    if (selected) seen++
  }
  selected && /_PreparedSheetContinuation_(advance|advanceCached|prepared|recentered)___/ {
    print "stored-data projection replays owner preparation: " $0 > "/dev/stderr"
    failed = 1
  }
  END {
    if (seen != 7) {
      print "expected seven stored-data projection implementations; found " seen > "/dev/stderr"
      failed = 1
    }
    exit failed
  }
' .lake/build/ir/Purelib/Riemann/Branches/PreparedSheetContinuation.c

printf 'All seven public projections select stored-data traversals without owner replay.\n'

if [[ $check_models == 1 ]]; then
  scripts/run-lake.sh --wfail --no-build build Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore:c
  scripts/run-lake.sh env leanc -DLEAN_EXPORTING -c \
    .lake/build/ir/Purelib/Riemann/Integration/PreparedDirectDyadicRefinementsCore.c \
    -o "$projection_tmp/ModelOwner.o"
  scripts/run-lake.sh env lean -DwarningAsError=true \
    -o "$projection_tmp/Model.olean" -c "$projection_tmp/Model.c" \
    Test/Riemann/Prepared/ModelProjections.lean
  if ! rg -q '_CenteredPathChain_dataOfCanonicalSubdivisionStored___redArg\(' "$projection_tmp/Model.c"; then
    printf 'canonical centered-data consumer did not select its stored-data implementation\n' >&2
    exit 1
  fi
  if rg -n '_PreparedSheetContinuation_(advance|advanceCached|prepared|recentered)___' "$projection_tmp/Model.c"; then
    printf 'canonical centered-data consumer replays owner preparation\n' >&2
    exit 1
  fi
  awk '
    /^LEAN_EXPORT.*\{/ {
      selected = ($0 ~ /_CenteredPathChain_dataOfCanonicalSubdivisionStored___redArg\(/)
      if (selected) seen++
    }
    selected && /_PreparedSheetContinuation_(advance|advanceCached|prepared|recentered)___/ {
      print "centered-data projection replays owner preparation: " $0 > "/dev/stderr"
      failed = 1
    }
    END {
      if (seen != 1) {
        print "expected one stored centered-data implementation; found " seen > "/dev/stderr"
        failed = 1
      }
      exit failed
    }
  ' .lake/build/ir/Purelib/Riemann/Integration/PreparedDirectDyadicRefinementsCore.c
  printf 'Canonical centered-data projection selects its stored-data traversal without owner replay.\n'
fi
