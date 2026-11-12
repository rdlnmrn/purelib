# Repository tools

Run Python implementations as modules from the repository root. The shell front
doors resolve that root themselves; the Python front doors share
`paths.py` startup. User-supplied relative paths retain the caller's working
directory. There are no installation dependencies or sibling import loaders.

| Command | Purpose |
| --- | --- |
| `scripts/run-lake.sh` | Checked Core prefix, patched native Lake driver, warning-fatal builds, builtin lint and optional build profiling |
| `scripts/check-all.sh --resume` | Full check plan with validated stage and individual-test restart |
| `scripts/check-all.sh --resume --release VERSION` | Check publication prerequisites before the full release checks |
| `scripts/build-papers.sh` | Regenerate the four main publication PDFs |
| `python3 scripts/worktrees.py {list,create,retire}` | Nested topic checkouts, current Git inventory and retirement with ignored-data preservation |
| `scripts/check-source.sh [FILE ...]` | Constructive policy over current source tokens; defaults to all active sources and configured script owners |
| `scripts/check-purelib-surfaces.py` | Current Lake ownership, publication/reusable boundaries and facade/executable coverage |
| `scripts/check-axioms.sh [MODULE_OR_FILE ...]` | Authoritative compiled proof closures, mandatory strict canonical support and independently audited fraction replay |
| `scripts/trace-axiom.sh` | Compiled axiom/use dependency diagnostics |
| `scripts/check-nanoda.sh` | Independent checker over the full active/configured inventory, or an explicit manifest |
| `scripts/check-prepared-projections.sh --models` | Complete C emission and stored-data projection regression |
| `python3 -m scripts.verification.namespace_prefixes [FILE ...]` | Rank long repeated namespace prefixes for manual source cleanup |
| `scripts/project-modules.py --configured-scripts` | Authoritative active module inventory; `--format path` emits sources |
| `scripts/project-module-data.py --help` | Pinned private/server/public/IR reader, contracts, dependencies and official-kernel type replay |
| `scripts/build-nanoda-profiler.sh` | Build the retained Rust diagnostic profiler |

The implementation families are `axioms`, `verification`, `lean_module_data`,
`nanoda`, `module_style`, `generators`, `linting`, `profiling` and `toolchain`.
Maintenance commands live in `maintenance`. The Core configuration and its
relative patch/template resources are checked together; prefix receipts bind
their exact configuration bytes. Native binaries and
checkpoints remain under `.lake`; a producer change creates a new request key
without rewriting old receipts or deleting compatible completed work.

Every build-wrapper invocation also runs the idempotent Lake scheduler installer:
`python3 -m scripts.toolchain.prepare_lake --prefix .lake/core-toolchain --cache
.lake/lake-toolchain`. The warm check reuses a validated native driver; the cold
path compiles the pinned dependency-join patch and relinks Lake without changing
the accepted Core epoch or installed Lean toolchain. See the [build-driver guidance](../docs/profiling.md#identify-the-expensive-phase)
for the scheduling failure and recovery. The repair covers native Lake CLI
builds; interpreted Lake API use retains the stock kernel and IR artifacts.
Run its native integration regression with:

```sh
CCL_TEST_CORE_PREFIX="$PWD/.lake/core-toolchain" \
  python3 -m unittest scripts.test.toolchain.test_lake
```

Examples:

```sh
python3 -m scripts.module_style.dependencies --module Purelib.Data.Fin --output /tmp/fin-dependencies.json
python3 -m scripts.verification.authored_names --help
python3 -m scripts.generators.critical_exterior_proofs
python3 -m scripts.generators.critical_exterior_proofs --two-parameter
python3 -m scripts.generators.sewing --input scripts/test/fixtures/sewing/annulus.json --output /tmp/Annulus.lean
python3 -m scripts.generators.sewing --input scripts/test/fixtures/sewing/annulus.json --output /tmp/Annulus.lean --check
python3 -m scripts.profiling.branch_builds --self-test
```

`critical_exterior_proofs` rewrites mathematical Lean proof schemas, and `sewing`
emits Lean regression sources. Follow the [generator verification requirements](../docs/verification.md#incremental-branch-checks)
when changing their mathematical output.

Constructor injectivity proofs are generated inside their owning Lean modules
by `constructive_injectivity TypeName` from
`Purelib.Elab.ConstructiveInjectivity`. The datatype metadata supplies the
complete constructor contract; there are no maintained field recipes, serialized
certificate terms or constructor JSON manifests. See
[constructor certificates](../docs/constructor-certificates.md) for the command,
its original `.inj`/Iff `.injEq` APIs and verification scope.

Namespace repetition analysis is source-only and needs no build or ripgrep:

```sh
python3 -m scripts.verification.namespace_prefixes
python3 -m scripts.verification.namespace_prefixes --limit 0
python3 -m scripts.verification.namespace_prefixes --json > /tmp/namespace-prefixes.json
python3 -m scripts.verification.namespace_prefixes Purelib/Examples/Geometry/Rotations/RotationAnchors.lean --min-uses 4
```

Defaults flag a prefix with at least three components and 24 characters used six
or more times across at least three lines. All four thresholds are configurable
with `--min-components`, `--min-prefix-chars`, `--min-uses` and `--min-lines`.
The default scope is every tracked or unignored current Lean file, including
examples, publications and fixtures. Reports ignore comments, literals, syntax
and name quotations, implicit notation quotations, declaration names, and
import/scope command headers, including their multiline continuations. Preserve
original qualified routes in notation expansions: Lean retains that syntax.
Capitalized components identify namespace-shaped prefixes; established lower-case
project roots are also accepted, while local field chains are excluded. This
convention can miss unusual lower-case namespaces and cannot resolve collisions.
Nested candidates share their source occurrences: a greedy ranking assigns each
use once, using the characters spent repeating the prefix after its first use.
That score ranks repetition; it is not guaranteed edit savings. Review the
reported lines before choosing a parent opening or a selective type opening;
existing openings, intentional disambiguation and retained compiler syntax can
justify a long route. The command does not edit files. The ordinary
`scripts/run-lake.sh lint` command runs it with the thresholds above over the
selected authored sources and fails on findings before building or starting
native lint workers.
`--json` emits every flagged file; `--check` optionally returns 1 for findings
(the ordinary report returns 0). Invalid input returns 2.

Source and surface checks use current files, imports and Lake configuration.
Regression modules check ownership, reduction and runtime contracts.

Compiled contract captures can include the current native query observation
with `python3 -m scripts.verification.contracts capture --snapshot OUTPUT.json
--module MODULE --observation`. The observation binds the built executable and
its complete metadata/private/IR inputs, and requires current default build
artifacts. Alternate artifact roots support declaration captures without a
native observation; they cannot borrow the current executable.

Scoped axiom requests retain their named proof scope and always add the fraction
runner as an independent project owner. The canonical backend inventory also
strictly checks every private/generated kernel declaration in its canonical
fraction-support owners. `--all-helpers` additionally selects every retained
kernel helper in the requested project modules. See the main
[verification instructions](../AGENTS.md).

## Task worktrees

Continue existing tasks in their current worktrees, including legacy locations.
For a new task, use the helper to create a fresh worktree on its topic branch:

```sh
python3 scripts/worktrees.py list
python3 scripts/worktrees.py list --json
python3 scripts/worktrees.py create new-topic
python3 scripts/worktrees.py retire new-topic
```

`create` checks out the named branch or creates it from `master`; `--base REV`
selects another starting revision for a new branch. It places the checkout under
the original root's ignored `.worktrees/`, using the branch name with slashes
and other separators converted to hyphens. Existing destinations, checked-out
branches and `master` are rejected. Keep each directory with its original task.

The helper recovers the original root when invoked from a nested checkout of
the same repository. An explicit `--root ORIGINAL_ROOT` before the subcommand
selects that root, including when inspecting or retiring legacy sibling trees.
The inventory comes directly from Git and includes locks, missing checkouts,
merge ancestry, working changes and ignored stores. It creates no manual registry.

`retire` accepts a branch name, task slug or registered absolute path. It requires
all commits to be contained in `master` (or the explicit `--base`), refuses
tracked changes, untracked files, locks, registered child worktrees and visible
process use, and retains the branch. Before removing the checkout, it moves all
ignored files and directories into `.worktrees/.retired/<topic>-<timestamp>-<id>/`
with a retirement receipt. This preserves caches, checkpoints and other ignored
work without copying whole stores. Cross-filesystem moves fail rather than
discarding data. A failed removal restores the stores when their original paths
remain available; otherwise the receipt identifies data retained in the archive.

Process checks inspect visible Linux working directories, executables and open
files. They cannot prove that another session has no planned work: finish or
coordinate with the owner before retiring its checkout. The helper never forces
removal, deletes branches, unlocks worktrees or prunes missing registrations.
Preserve detached tips before separately pruning stale registrations. Archived
data remains available for deliberate reuse or later cleanup.

Run the helper regressions with:

```sh
timeout --signal=TERM --kill-after=15s 300s python3 -m unittest scripts.test.maintenance.test_worktrees
```

## Test modes

Tests are ordinary `test_*.py` package modules under `scripts/test`. Intentional
negative Lean inputs are under `test/fixtures`, retain isolated module identities
and output roots, and are excluded from active/configured proof discovery.

### 1. Fast host controls

These do not build Lean or run the independent checker:

```sh
python3 -m unittest \
  scripts.test.module_style.test_core \
  scripts.test.module_style.test_contracts \
  scripts.test.generators.test_sewing \
  scripts.test.verification.test_authored_names \
  scripts.test.verification.test_checkpoints \
  scripts.test.verification.test_declarations \
  scripts.test.verification.test_imports \
  scripts.test.verification.test_reader_provenance \
  scripts.test.verification.test_source_policy \
  scripts.test.verification.test_surfaces \
  scripts.test.axioms.test_orchestration \
  scripts.test.axioms.test_trace \
  scripts.test.axioms.test_propext_frontier \
  scripts.test.profiling.test_build_costs \
  scripts.test.linting.test_runner \
  scripts.test.linting.test_configuration.ProviderPreparationTests \
  scripts.test.linting.test_configuration.DefaultScopeTests \
  scripts.test.nanoda.test_benchmark_pipeline \
  scripts.test.nanoda.test_compare_exports \
  scripts.test.nanoda.test_export_validation \
  scripts.test.nanoda.test_planning \
  scripts.test.nanoda.test_scheduling
python3 -m scripts.test.nanoda.test_check_cache
python3 -m scripts.test.nanoda.test_input_key
python3 -m scripts.test.nanoda.test_graph_cache
python3 -m scripts.profiling.branch_builds --self-test
```

The last four commands have actual CLI `main` controls. Unittest discovery alone
does not run them.

### 2. Compiling/artifact/checker integration

Build the project with `scripts/run-lake.sh --wfail build` first. Install/build the
pinned independent checker as described in [nanoda](nanoda/README.md), or set
`NANODA_BIN`. Use the wrapper's environment for the current checked Core prefix:

```sh
scripts/run-lake.sh env python3 -m unittest \
  scripts.test.axioms.test_backend \
  scripts.test.axioms.test_module_fixtures \
  scripts.test.lean_module_data.test_reader \
  scripts.test.lean_module_data.test_kernel_equivalence \
  scripts.test.verification.test_contracts \
  scripts.test.linting.test_configuration.NativeLinterTests \
  scripts.test.nanoda.test_check_stream \
  scripts.test.nanoda.test_native_export \
  scripts.test.nanoda.test_policy \
  scripts.test.nanoda.test_root_inventory
scripts/check-prepared-projections.sh --models
```

The kernel fixture test compiles current isolated before/after inputs, invokes the
manifest CLI itself, checks exact success/missing-name transport, and requires
an actual official-kernel rejection of a changed type. Reader tests require real
pinned artifacts and fail when they are unavailable. There are no silent skips.
Every standalone native regression must also run its required modes below.

For a complete unittest pass use
` scripts/run-lake.sh env python3 -m unittest discover -s scripts/test -t . -p 'test_*.py' `,
then run the explicit mode-1 CLI commands. Serialize project builds and artifact
readers; integration fixture compilers write only isolated temporary outputs.

### 3. Explicit replay/performance inputs

For a retained kernel request, invoke the control with a nonempty manifest:

```sh
python3 -m scripts.test.lean_module_data.test_kernel_equivalence MANIFEST.json \
  --toolchain TOOLCHAIN --cache CACHE --output OUTPUT
```

The schema-1 manifest binds each input `path`/`sha256` and each case's `case`,
`lean_path`, ordered `arguments`, `exit`, `stdout_base64` and `stderr_base64`.
Missing/stale inputs, missing manifests, duplicate cases and output differences
fail. Current compiling fixtures also exercise this command in mode 2.

Performance commands require actual input scope; they are not implicit tests:

```sh
python3 -m scripts.nanoda.export_graph --manifest scripts/nanoda/benchmarks/control.modules
python3 -m scripts.nanoda.graph GRAPH.jsonl --stream EXPORT.ndjson --costs
python3 -m scripts.nanoda.benchmark_checker EXPORT.ndjson --jobs 1 2
python3 -m scripts.nanoda.benchmark_pipeline --manifest scripts/nanoda/benchmarks/control.modules --output OUTPUT
```

The existing benchmark manifests remain under `nanoda/benchmarks`. Use current
checked artifacts and preserve completed, input-bound stages. The Rust profiler
source is `profiling/Nanoda.rs`.

## Numerical workloads

Three drivers cover distinct construction chains without generated certificate
fixtures. Build their targets once, then run `.lake/build/bin/EXECUTABLE`:

| Executable | Input and result |
| --- | --- |
| `initial_isolation_harness` | `real`, `negative`, `complex`, `cubic`, `period-cubic` or `all`: compute squarefreeness and isolate every root from exact coefficients; check counts, separation and winding data |
| `square_factor_observation_harness` | `budget LAYER`: report coefficient bounds and resolution for `y² = x²(x³+1)`; `observe BIT_COUNT`: integrate the original-coordinate differential along `[1,17/16]` and check accuracy and source-free replay |
| `canonical_period_preparation_harness` | `DEPTH`: prepare the first canonical cycle of the same curve's squarefree reduction and attempt its four complete path banks at that dyadic depth |

Period preparation reports either accepted bank sizes or an inconclusive finite
attempt with its failed prefix and obstruction. It performs one supplied depth;
it produces no period value. Observation can be expensive even for a short bit
prefix; use the square-factor budget report to inspect its computed resolution.

`project_query_replay_observation` supplies the native observation used by
compiled contract captures above.

## Standalone Lean regression coverage

Shared checkpoint implementations are owned by `checkpoint`, observations by
`observations` and benchmarks by `profiling`. Each reusable module has one Lake
library owner.
`TestPurelib.All` covers ordinary regressions and projection consumers; standalone global
`main` modules are covered through their declared executable import closures.
`decimal_regression` runs the decimal renderer checks; `decimal_balanced_benchmark`
only times the two explicitly supplied codec fixtures.

Run these after building their named executables. Each checkpoint command needs
its own fresh directory, such as `/tmp/ccl-replay-TEST`:

| Executable | Required regression modes |
| --- | --- |
| `enclosure_observer_regression` | No arguments; enclosure execution and imported-record checks |
| `ccl_cursor_continuation_regression` | No arguments; all eight continuation groups (`--case NAME` selects one) |
| `fraction_regression` | No arguments; also executed by the authoritative axiom command |
| `io_reference_regression` | No arguments; original reference identity, shared updates, retained snapshots and cache writes preceding errors |
| `integration_replay_regression` | No arguments |
| `adaptive_prepared_banks_harness` | No arguments |
| `integration_checkpoint_harness` | `selftest DIRECTORY` (includes restart, corruption, source-free replay, import, certified/stateful and partial replies) |
| `polynomial_inverse_checkpoint_harness` | `self-test DIRECTORY` |
| `canonical_isolation_checkpoint_harness` | `self-test`, `family-self-test`, `frame-self-test`, `grid-frames-self-test`, `subdivision-self-test`, `newton-self-test`, each with a fresh directory; `newton-resume-test` on its completed Newton directory |

`check-prepared-projections.sh --models` checks both projection sources
through complete C output and C compilation. It requires the owner C artifacts
to be current from the preceding warning-fatal build; stale/missing artifacts
fail rather than launching redundant export-info jobs. Standalone regression
and profiling targets retain their own CLI contracts and full proof/build
coverage; they are not facade imports.
