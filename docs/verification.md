# Completion checks

Before completing work, run the full suite from any directory:

```sh
/path/to/repo/scripts/check-all.sh --max-cores 32
```

Omit `--max-cores` to use all available cores. On Linux the runner restricts CPU
affinity for its entire child process tree, including compiler and Rust threads.
The flag counts logical CPUs, capped by the invoking process's existing affinity.
From the repository root, use `scripts/check-all.sh`. `--list` shows all commands
without running them. The script fails at the first failed gate and returns its
exit status; only a successful complete invocation establishes a full pass.
Freeze source and tooling edits and serialize other Lean builds and checks in
this worktree for the duration of the run.

The gates are constructive source policy, source/build coverage, the full
warning-fatal build, the compiled unreserved sharpness regression, all
discovered tooling tests, the three standalone cache
regressions, restart recovery, prepared projection code-emission regressions,
all-source warning-fatal lint, the normal full axiom audit including configured
script owners, and the full nanoda check. Strict `--all-helpers` audits remain a
separate scope. Builds include all configured optional targets; they compile
observation harnesses without launching their expensive observations.

Build and artifact-consuming stages run sequentially. Lint uses `--no-build`
after the full build; the audit and nanoda retain their own mandatory incremental
build/currentness gates and support preparation. Their existing content-checked
caches reuse successful work, including after interruption. The completion
runner never skips a stage based on a previous run's summary. Tooling tests run
once through discovery, with individual tests distributed across isolated worker
processes. Each worker inherits one assigned core and uses separate temporary
fixture outputs against the stable project artifacts. Shared native helper
caches have their own build locks. The assertion-based cache scripts and profiling
self-test run separately because unittest discovery does not execute them.

Each invocation retains combined output for every stage, timings, exit codes
and a summary under `.lake/completion-checks/<timestamp>/`. The runner checks
tracked and unignored new file contents before and after all gates and rejects
a pass if the tree changed. Reports describe the run; they do not replace the
checkers' receipts. Repeating the command revalidates the current tree and reuses
compatible child-checker checkpoints.
Individual test logs and a complete discovery/coverage report live in that
run's `tooling-tests/` directory. The report includes peak active workers and
sampled combined process-tree RSS. Failure or interruption cancels owned worker
descendants, including helpers with independent sessions.

The pinned Lake task panic still requires the default `LEAN_NUM_THREADS=1`
scheduling workaround. Set it explicitly to override that default. This limits
each Lean runtime rather than the independent lint, axiom and nanoda worker
pools. Quiet builds suppress informational replay while retaining warning-fatal
checking and failure diagnostics.

Automatic lint, audit, tooling and nanoda pool sizes use available host memory, leave a quarter
in reserve, and cap the memory budget at 250 GiB. Their estimates are two GiB per
lint worker and twelve GiB per complete audit worker. Reviewed small tooling
fixtures reserve two GiB; heavy fixtures and newly discovered modules reserve
twelve GiB. The scheduler starts another test whenever both a core and its
memory reservation are free. Without a memory reading,
the defaults are at most eight lint workers and two audit workers. Explicit
`CCL_LINT_JOBS`, `AXIOM_AUDIT_JOBS`, `CCL_TOOLING_JOBS` and nanoda settings can
lower parallelism; the runner clamps them to its core and memory budgets.
Nanoda budgets simultaneous exporters and checker instances together, reserving
sixteen GiB per process from a measured full-inventory peak of 12.4 GiB. Checker
instances retain at least two threads to use the pinned checker's normal worker
stacks. On small core or memory budgets, exports and checks run separately; a
single-core invocation pins both checker threads to that core. Hosts smaller
than a heavyweight reservation still run one such job at a time. Reservations
are scheduling estimates, not operating-system memory limits.

The runner aggressively distributes independent work within these constraints.
Shared-artifact stages remain serialized, and individual tests or dependency
chains can leave cores idle at the end of a stage. More cores cannot remove the
Lake scheduling workaround or the memory cost of duplicated decoded imports.

CI uses this same runner. Its explicit Lean cache is restored before setup and
saved only after a successful complete pass, so it includes newly produced
build, lint, axiom and nanoda checkpoints. The restore fallback binds the pinned
toolchain, dependency manifest and Core producer inputs. Profiling runs and
historical experiments are excluded. Mathlib's artifact download remains
enabled; the setup action's earlier GitHub-cache save is disabled. Rust has a
separate cache including the pinned checker crate and its release build, and
Cargo still validates the build on every run. Completion reports are uploaded
as artifacts even on failure. GitHub storage limits and eviction can reduce
cache availability; checker receipts still validate every restored input.

Build the pinned nanoda checker under `.external/nanoda` first, or set
`NANODA_BIN` to an existing checker executable. The runner checks its availability
before starting expensive work. `NANODA_MODULE_MANIFEST` is rejected because
completion must cover the full active inventory. See the [README](../README.md)
for checker setup, focused branch checks and cache contracts, and
[linting](linting.md) for linter coverage. Documentation-only work and tooling
exceptions retain the requirements in [AGENTS.md](../AGENTS.md); invoking the
full suite is always a stronger check.
