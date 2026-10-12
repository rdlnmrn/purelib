#!/usr/bin/env bash
set -euo pipefail

# Invoke inside systemd-run MemoryMax/MemorySwapMax and an explicit
# timeout --signal=KILL.  This runner does not build or change Lean limits.
if [[ $# != 3 || ! $1 =~ ^(a|b)$ || ! $2 =~ ^[0-9]+$ ]]; then
  printf 'usage: profile-period-observation.sh a|b BIT_COUNT CHECKPOINT_DIRECTORY\n' >&2
  exit 2
fi
repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
checkpoint_dir=$(realpath -m -- "$3")
case "$checkpoint_dir" in
  "$repo_root"/.lake/period-checkpoints/*) ;;
  *) printf 'checkpoint directory must be beneath .lake/period-checkpoints/\n' >&2; exit 2 ;;
esac
mkdir -p -- "$checkpoint_dir"
observation_exe="$repo_root/.lake/build/bin/polynomial_period_observation_harness"
run_log=$(mktemp "$checkpoint_dir/run.XXXXXX.log")
resource_log=$(mktemp "$checkpoint_dir/resources.XXXXXX.log")
cd "$repo_root"

"$observation_exe" observe "$1" "$2" "$checkpoint_dir" >"$run_log" 2>&1 &
observation_pid=$!
pidstat -h -u -r -w -t -p "$observation_pid" 30 >"$resource_log" 2>&1 &
sampler_pid=$!
cleanup() {
  if kill -0 "$sampler_pid" 2>/dev/null; then
    kill "$sampler_pid" 2>/dev/null || true
  fi
  wait "$sampler_pid" 2>/dev/null || true
}
trap cleanup EXIT
printf 'Observation PID=%s; phase log=%s; resource log=%s; CPU ticks/second=%s\n' \
  "$observation_pid" "$run_log" "$resource_log" "$(getconf CLK_TCK)"

result=0
wait "$observation_pid" || result=$?
tail -n 80 "$run_log"
if [[ $result == 0 ]]; then
  # A separate process proves the replay command does not need the retained
  # in-memory source or its canonical preparation.
  "$observation_exe" replay "$checkpoint_dir" "$2"
fi
exit "$result"
