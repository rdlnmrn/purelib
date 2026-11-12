# Branch checks and master integration

## Incremental branch checks

During branch work, incrementally build, axiom-check and lint changed modules and
affected consumers after meaningful batches and before checkpoint commits:

```sh
scripts/run-lake.sh --wfail build MODULE
scripts/check-axioms.sh MODULE
scripts/run-lake.sh --wfail lint MODULE
```

Agents decide when to make coherent commits. Always use a topic branch unless
the user explicitly permits `master`. Continue existing tasks in their current
worktrees, including legacy locations. For a new task, create a fresh worktree
with `python3 scripts/worktrees.py create TOPIC`. New worktrees, including those
used by subagents, belong inside the original top-level worktree under `.worktrees/`.
Use `list` to inspect existing worktrees and `retire TOPIC` after completion;
see the [worktree procedure](../scripts/README.md#task-worktrees).
See [AGENTS.md](../AGENTS.md) for the full working rules.

Nanoda and the full suite are merge-readiness checks. They are not required at
each checkpoint or merely to complete a branch implementation. Run nanoda earlier
only when explicitly requested or needed for a specific diagnosis; report pending
integration checks separately from incremental branch verification.

Changes to generators of mathematical Lean sources require checking the generated
sources and their consumers as well as producer regressions. This includes
`scripts.generators.critical_exterior_proofs` and `scripts.generators.sewing`.
Lint/checker tooling has the narrower exceptions in [AGENTS.md](../AGENTS.md);
other scripts receive focused tooling checks when they neither change nor
generate mathematical Lean sources. Documentation-only changes need no Lean
build or proof audit.

## Preparing an integration

Integrate only when requested. `git merge --no-commit` alone cannot hold a
fast-forward for verification: Git advances the branch immediately. Combine
`--no-ff --no-commit` to stop before a merge commit. The installed Git manual
documents this behavior under `git help merge`.

A staging branch keeps the candidate off `master` until the checks pass. Start
with a clean task tree and current local `master`, then, using task-specific names:

```sh
git switch -c integrate/TASK master
git merge --no-ff --no-commit TOPIC
```

Resolve conflicts, build the combined tree, and fix slow compilation in the
affected scope described below. Run applicable incremental checks after fixes,
then the applicable full integration gates on the finished candidate. The full
suite already includes the warning-fatal build. Use controlled fresh measurements
for affected slow modules; a successful build alone does not certify timing.
Only after these checks pass, stage the task's final resolution and fixups,
commit the merge, switch to `master`, and promote it with
`git merge --ff-only integrate/TASK`.

If `master` advances before promotion, incorporate its new state into the staging
branch and repeat the affected checks and final gates on the combined tree.
Do not force promotion past a diverged `master`. A merge staged directly on
`master` uses the same `--no-ff --no-commit` pause when that workflow is authorized;
the staging branch is preferable for keeping all unfinished work on a branch.
Fixes can be committed on the topic branch before staging the final merge where
practical. Preserve any candidate-only fixes before discarding a staged merge.

## Full integration checks

When ready to integrate into `master`, run the applicable full suite from any directory:

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
warning-fatal build, the compiled decimal-rendering and unreserved sharpness regressions,
the compiled enclosure-observer and cursor-continuation regressions, the coded-machine
simulation, domain-observer coverage and integration replay regressions, all discovered tooling
tests, the three standalone cache regressions, restart recovery, prepared
projection code-emission regressions,
all-source warning-fatal lint, the normal full axiom audit including configured
script owners, and the full nanoda check. Strict `--all-helpers` audits are
optional diagnostics of a separate scope, not a producer-purity requirement.
Builds include all configured optional targets; they compile
observation harnesses without launching their expensive observations.

The enclosure and continuation gates invoke their native Lean executables
directly. The continuation gate runs all eight named regression groups;
acceptance, invalidity, inconclusive candidates and later requests are checked
using Lean records in memory. The tests require no persistent fixture store.

Build and artifact-consuming stages run sequentially. Lint uses `--no-build`
after the full build; the audit and nanoda retain their own mandatory incremental
build/currentness gates and support preparation. Their existing content-checked
caches reuse successful work, including after interruption. The completion
runner never skips a stage based on a previous run's summary. Tooling tests run
once through discovery, with individual tests distributed across isolated worker
processes. Each worker inherits one assigned core and uses separate temporary
fixture outputs against the stable project artifacts. Each individual tooling
test has a five-minute watchdog and a fifteen-second termination grace; the
aggregate test suite may run longer. Shared native helper
caches have their own build locks. The assertion-based cache scripts and profiling
self-test run separately because unittest discovery does not execute them.

An explicitly authorized exception can select a deadline of at most ten minutes
for an exact discovered test ID through `CCL_TOOLING_TIMEOUT_OVERRIDES`, a JSON
object mapping IDs to seconds. Unknown IDs and invalid or unbounded values fail
before preparation. Other tests retain their five-minute watchdog. Each selected
deadline is recorded and bound to that case's checkpoint; changing an unrelated
case's exception does not invalidate it. Workers do not receive this supervisor
configuration. Do not raise a deadline automatically after a timeout.

Use `scripts/check-all.sh --resume --max-cores 5` to retain and reuse completed
checks in `.lake/completion-checkpoints/`. Build, lint, axiom and nanoda gates
still run their own artifact-currentness and checkpoint validation. Other stages
can reuse a successful execution with unchanged inputs and retained output.
Tooling discovers the full inventory again and reuses individual completed
cases, selecting only unresolved cases for execution. If every Horner case is
already validated, it does not prepare another supplied-body session. Pending
Horner cases still require a new live producer witness; a saved producer receipt
cannot supply one.

With `--resume`, independent tooling cases finish and checkpoint before a pending
Horner session is prepared. An independent failure therefore stops the run before
producer compilation. After readiness, the worker validates the complete
inventory again and reuses those independent results before running Horner cases.

Reusable checks bind commands, configuration, executable interpreters and shared
libraries, source dependencies and complete public/private/server/IR artifacts
where required. Mathematical input groups are conservative; test implementation
groups include package owners and imported Python helpers. Absolute literal
`__import__` calls bind their module and literal `fromlist` owners like ordinary
imports. Unknown dynamic Python loading falls back to all Python sources.
Native Rust tooling has a separate
binding, so rebuilding its library need not invalidate completed Horner cases.
Execution removes per-launch systemd diagnostic IDs and cgroup paths before
binding and passing the environment to checks. Isolated test workers also omit
the suite's tooling/lint pool sizes and changing memory-headroom budget; fixtures
retain their own explicit budgets and the enforced process limits. Other worker
configuration and selected case deadlines remain inputs. A supervisor restart
can therefore reuse an unchanged completed case.
Changed input groups and damaged output records are reported before rerunning
their checks. Shared input manifests and successful logs are retained separately
from each invocation's summary, with atomic completion records.

Resume uses the same worktree lock and serialized artifact access as an ordinary
run. A failed or interrupted invocation can retain completed checks while its
summary remains failed or interrupted. Final acceptance still requires exact
coverage of the newly discovered inventory. Reused timings describe the previous
execution; they do not establish fresh compilation or performance measurements.
Omit `--resume` to execute every stage and test again while still using the
underlying build and proof checkers' validated artifact caches.

Before the source gates, the runner exercises local socket communication and
links the native nanoda adapter against the selected Rust library. Tooling also
checks the C adapter before preparing an unresolved supplied-body session.
Failures stop preparation early; repair incompatible native libraries with the
pinned sources and current compiler. `preflight.json` records these steps,
including failures and interruptions. Tooling's `setup.json` distinguishes input
binding, producer compilation and client execution; a readiness message marks
when the live producer can answer requests.

For a release, use `scripts/check-all.sh --resume --release VERSION` on its clean
private source checkout. Publication preflight checks local history records,
projection and tag correspondence, and performs an atomic push dry run before
the source gates. The intended private commit is checked again at completion.
Preflight creates no successful publisher receipt and changes no remote refs.
The publisher still requires its normal exact-source checks before publication.

While a stage runs, the terminal receives an elapsed-time update every 30 seconds,
including how long it has been since the last child output. Python workers use
unbuffered output. These updates also appear in CI, including during quiet builds;
they report liveness, not a completion estimate. Per-stage logs retain the exact
child output.

## Durable release checkpoints

Reuse the topic worktree named by local Git configuration `ccl.releaseWorktree`
for progressive releases. Advance its clean branch to the intended `master`
commit with `--ff-only`, retaining its absolute path and ignored build/check
stores. Run the completion suite and publisher checks in that same checkout.
Publisher operations require its HEAD to equal the configured source branch;
unintegrated topic changes cannot be published accidentally.

Keep hot compiler/build outputs and large lint stores local. A private writable
NFS store can retain completion records, axiom passes and nanoda checkpoints at
stable paths.
Check the mount, space, permissions, atomic flush/rename and locking before use.
Move stores only after their owned workers have exited, keep one writer and the
worktree lock, and preserve all currentness checks on reload. Back up local
toolchain/build/lint caches after a stopped or completed run as well; use a single
compressed archive when per-file NFS metadata operations dominate the copy.

Publication mappings and successful-check receipts are separate from suite logs.
The private publisher supports an external directory through
`ccl.publicHistoryStore` and automatically bundles mapping notes beside receipts.
Fetch source/public commits and release tags before restoring those records into
a new checkout. Restoration preserves existing divergent notes and still requires
ordinary history and proof-check validation. A copied cache or saved report alone
does not establish current artifacts, producer provenance or a release pass.

## Timing scope and measurement

Before integration into `master`, changed project modules and consumers affected
by their changes must each compile in under 30 seconds, including complete
artifact/code emission. Nanoda module checks in that affected scope have the
same target. A branch implementation may be complete with documented timing
debt. Keep correctness checks and report any blocked gate as failed or incomplete.
Third-party code is outside the 30-second target.

An unchanged module's compilation can become slower through changed dependencies:
exposed bodies and inlining affect reduction and native code generation, while
changed instances, notation and elaborator registrations affect elaboration.
Start with edited modules and their relevant reverse import/consumer closure;
inspect actual recompilations and timing warnings in the full build. Include
changes made during conflict resolution. Changes to shared mathematical
generators, toolchain inputs or build configuration can broaden that scope.
Rebuilding a module does not by itself require detailed profiling: investigate
affected modules whose complete compilation reaches the target or regresses.
No profiling or performance cleanup is required for unaffected modules. Report
observed unrelated overruns separately; they do not expand this timing task.
If an unchanged consumer is already slow and attribution is unclear, compare it
with `master` under the same conditions. An existing overrun unchanged by this
work does not become a cleanup requirement.

Compare quiet runs on the integration host with current dependencies, the same
thread settings and CPU affinity, and no competing heavy jobs. Record that
environment and report variability rather than selecting the fastest run.
The 30-second target applies to these controlled complete compilations; use
contended broad-build warnings to identify candidates for measurement. A cache
hit establishes no fresh compilation time. Reuse measurements only when their
source, toolchain, options and relevant dependency artifacts still agree.
Use the [profiling guide](profiling.md) for isolated measurement and diagnosis;
an optional full cold build provides broader coverage than this affected scope.

The current Lean compiler guard records timings and warns at 30 seconds; the
integration procedure requires reviewing affected timings before committing.
There is no automatic Git merge or commit rejection for a slow Lean module.
The current nanoda scheduler and receipt validator reject checks reaching
30 seconds on every branch and for every exported owner, including unaffected
and third-party owners. That broader enforcement has not yet been aligned with
the affected-project scope. An out-of-scope nanoda timing failure must be reported
as such; it still prevents claiming a successful full nanoda pass.

## Watchdogs and process ownership

Every individual module build must be launched under a two-minute wall-clock
watchdog by default, followed by a fifteen-second termination grace. `scripts/run-lake.sh`
guards project Lean compilation; the cold Core compiler workers and standalone
profiling compilations enforce the same deadline. Nanoda module checks and
regression tests retain their five-minute watchdogs. The full-suite
runner supervises regression executables and individual tooling tests. Standalone
regressions need equivalent supervision; a tool call yielding early is not a timeout.
Terminate at the deadline and investigate immediately before retrying or continuing
dependent work. A timeout fails even if the child exits zero while handling termination.
The raw child exit is recorded before closing streams. Full builds, lint, axiom
audits, tooling-test suites and full nanoda runs may exceed five minutes in aggregate, with progress
reporting and owned-process supervision retained. Other stages keep the
five-minute deadline. Preserve completed results and the full final scope when
diagnosing an overrun.

An explicit user-authorized release exception may set
`CCL_MODULE_TIMEOUT_SECONDS=300` for guarded Lake compilation. Values must be
finite, positive and at most 300 seconds; the default remains 120 seconds.
Select this budget deliberately after diagnosing any overrun, and keep it fixed
throughout the release checks. Each module receipt records its actual limit;
the guard binding and completion checkpoints also bind the selected budget.
This setting changes neither Lean's heartbeat/reduction limits nor regression,
numerical-job or nanoda-checker deadlines. A larger deadline is not a performance
measurement or a proof that an interrupted attempt succeeded.

Preserve the owning wait if progress reporting or log persistence fails. Record
the raw exit before closing streams or inspecting group/log metadata. Retain
those errors and reject acceptance on them. Before restarting or replacing a
job, verify the identities of its supervisor and descendants, stop them, and
confirm that no superseded worker survives, including detached descendants.

## Artifact currentness and audit coverage

`--no-build` requires current selected and audit-support artifacts. Audit receipts
bind module sets, source/tool revisions and complete compiled private artifacts,
including generated proof auxiliaries. A public `.olean` alone establishes no
private-body currentness. After proof-dependency changes, rebuild the affected
import closure. Literal `ConstantInfo` equality does not establish current
exported-axiom cache entries; retain those entries and bind complete emitted
parts. Missing or stale private artifacts require rerunning the authoritative
audit.

The host artifact reader hashes complete files with bounded streaming reads.
Serialized bytes use a shared 128 MiB page cache rather than a retained copy of
every imported file. An evicted page is reloaded only from the same unchanged
file incarnation; replacement, truncation or a missing file fails the read.
The import graph shares structurally identical decoded nodes across modules,
while keeping pointer caches and import ownership separate. The axiom audit
validates expression graphs in temporary decoders and retains ordered dependency
names instead of every decoded proof. Persisted axiom tables and the complete
original import environment still determine the closure traversal.
Decoded metadata and dependency edges require memory in addition to the byte
cache. Keep artifact writers serialized and retain complete input
bindings; bounded storage does not change proof coverage or provenance.

The core budget also applies inside a library audit. The parent loads one complete
import environment and selects the roots. It seals the root inventory and releases
temporary decoder indexes after loading the persisted first-owner tables. Small
workers decode the original bound declarations; the parent resolves their names
against the retained environment.

The resulting immutable graph shares name prefixes, payload bytes and identical
dependency lists. Before use, the parent checks every name, owner, cached entry,
axiom/reference flags and ordered dependency list against its original observations.
Linux memory-file seals prohibit writes, growth and truncation; query workers map
the same buffers read-only and use the original closure traversal. Results retain
their original query order and canonical/helper scope. Missing replies, worker
crashes and interruptions prevent a pass.

`--max-cores N` divides the CPU budget between independent audit environments
and their worker pools. Decoder workers reserve 512 MiB each; query workers reserve
128 MiB each in addition to the shared graph. Current host and cgroup headroom
can reduce concurrency. Initial import loading remains serial. Direct
`scripts/check-axioms.sh` invocations retain their existing defaults; set
`CCL_CHECK_CORES=N` to supply the same total budget outside the completion runner.

Include configured script owners explicitly in full audits:
`scripts/check-axioms.sh --configured-scripts --full`. Plain `--full` omits them.
When changing audit coverage or receipt validation, identify script roots by
scanned module and declaration name; standalone modules can share the basename
`main`. Include selected project roots even when their worker labels them
canonical. Worker roles do not change declaration identity or project coverage.

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

The installed patched native Lake CLI supports parallel compilation.

The completion runner still defaults to `LEAN_NUM_THREADS=1` as a scheduling
choice. Set an explicit value, such as `LEAN_NUM_THREADS=8`, to select parallel
Lean execution within the runner's core budget. This controls each Lean runtime
separately from the lint, axiom and nanoda worker pools; shared-artifact stages
remain serialized. Quiet builds retain warning-fatal checks and failures.

Automatic lint, audit, tooling and nanoda pool sizes use the smaller of available
host memory and inherited cgroup v2 headroom, including ancestor `memory.high`
and `memory.max` limits. They leave a quarter in reserve and cap the memory
budget at 250 GiB. Their estimates are two GiB per
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
chains can leave cores idle at the end of a stage. More cores cannot remove
sequential dependencies or the memory cost of duplicated decoded imports.

CI uses this same runner for pushes to `master`, non-draft pull requests targeting
`master` and explicit manual runs. Routine topic-branch pushes and draft pull
requests do not launch the full merge-readiness suite. Its explicit Lean cache is restored before setup and
saved only after a successful complete pass, so it includes newly produced
build, lint, axiom and nanoda checkpoints. The restore fallback binds the pinned
toolchain, dependency manifest and checked Core/frontend producer inputs.
Profiling runs and historical experiments are excluded. Mathlib's artifact
download remains enabled; the setup action's earlier GitHub-cache save is disabled. Rust has a
separate cache including the pinned checker crate and its release build, and
Cargo still validates the build on every run. Completion reports are uploaded
as artifacts even on failure. GitHub storage limits and eviction can reduce
cache availability; checker receipts still validate every restored input.

Build the pinned nanoda library under `.external/nanoda` first. The runner links
the module scheduler to this unchanged kernel library and checks every exported
declaration once on the shared graph, grouped by independently read compiled
owners. Module timings exclude shared parsing and preparation. Each nanoda module
check retains its five-minute watchdog; the current checker also enforces its 30-second
performance gate as described above. Checker receipts bind
the scheduler binary, exact graph, configuration and compiled ownership map;
they retain the per-module counts and timings. Selecting the pinned stock CLI
with `NANODA_BIN` also uses this scheduler. Another selected checker must
implement the same `CONFIG --modules OWNERS` protocol. Failed checks
retain their frozen inputs, raw exit and diagnostics without publishing success.
`NANODA_MODULE_MANIFEST` is rejected because
completion must cover the full active inventory. See the [README](../README.md)
for checker setup, focused branch checks and cache contracts, and
[linting](linting.md) for linter coverage. Documentation-only work and tooling
exceptions retain the requirements in [AGENTS.md](../AGENTS.md); invoking the
full suite is always a stronger check.
