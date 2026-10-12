# Repository tools

Run Python implementations as modules from the repository root. The shell front
doors resolve that root themselves; the three retained Python front doors share
`paths.py` startup. User-supplied relative paths retain the caller's working
directory. There are no installation dependencies or sibling import loaders.

| Command | Purpose |
| --- | --- |
| `scripts/run-lake.sh` | Checked Core prefix, patched native Lake driver, warning-fatal builds, builtin lint and optional build profiling |
| `scripts/build-papers.sh` | Regenerate the four main publication PDFs |
| `scripts/check-source.sh [FILE ...]` | Constructive policy over current source tokens; defaults to all active sources and configured script owners |
| `scripts/check-purelib-surfaces.py` | Current Lake ownership, publication/reusable boundaries and facade/executable coverage |
| `scripts/check-axioms.sh [MODULE_OR_FILE ...]` | Authoritative compiled proof closures, mandatory strict canonical support and independently audited fraction replay |
| `scripts/trace-axiom.sh` | Compiled axiom/use dependency diagnostics |
| `scripts/check-nanoda.sh` | Independent checker over the full active/configured inventory, or an explicit manifest |
| `scripts/check-prepared-projections.sh --models` | Complete C emission and stored-data projection regression |
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
python3 -m scripts.module_style.manifest --regenerate
python3 -m scripts.module_style.manifest --check
python3 -m scripts.module_style.dependencies --module Purelib.Data.Fin --output /tmp/fin-dependencies.json
python3 -m scripts.verification.authored_names --help
python3 -m scripts.generators.critical_exterior_proofs
python3 -m scripts.generators.critical_exterior_proofs --two-parameter
python3 -m scripts.generators.sewing --input scripts/test/fixtures/sewing/annulus.json --output /tmp/Annulus.lean
python3 -m scripts.generators.sewing --input scripts/test/fixtures/sewing/annulus.json --output /tmp/Annulus.lean --check
python3 -m scripts.profiling.branch_builds --self-test
```

Constructor injectivity proofs are generated inside their owning Lean modules
by `constructive_injectivity TypeName` from
`Purelib.Elab.ConstructiveInjectivity`. The datatype metadata supplies the
complete constructor contract; there are no maintained field recipes, serialized
certificate terms or constructor JSON manifests. See
[constructor certificates](../docs/constructor-certificates.md) for the command,
its original `.inj`/Iff `.injEq` APIs and verification scope.

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
  scripts.test.module_style.test_public_imports \
  scripts.test.generators.test_sewing \
  scripts.test.verification.test_authored_names \
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
checked artifacts and preserve completed, input-bound stages. Profiling retained
period observations uses `scripts/profiling/period_observation.sh`; the Rust
profiler source is `profiling/Nanoda.rs`.

## Standalone Lean regression coverage

Checkpoint implementations are owned by `checkpoint`, observations by `observations` (saved replay under `saved`) and
benchmarks by `profiling`. Each reusable module has one Lake library owner.
`Test.All` covers ordinary regressions and projection consumers; standalone global
`main` modules are covered through their declared executable import closures.

Run these after building their named executables. Each checkpoint command needs
its own fresh directory, such as `/tmp/ccl-replay-TEST`:

| Executable | Required regression modes |
| --- | --- |
| `fraction_regression` | No arguments; also executed by the authoritative axiom command |
| `integration_replay_regression` | No arguments |
| `adaptive_prepared_banks_harness` | No arguments |
| `integration_checkpoint_harness` | `selftest DIRECTORY` (includes restart, corruption, source-free replay, import, certified/stateful and partial replies) |
| `polynomial_inverse_checkpoint_harness` | `self-test DIRECTORY` |
| `canonical_isolation_checkpoint_harness` | `self-test`, `family-self-test`, `frame-self-test`, `grid-frames-self-test`, `subdivision-self-test`, `newton-self-test`, each with a fresh directory; `newton-resume-test` on its completed Newton directory |
| `prepared_source_replay_harness` | `self-test`, `bank-self-test`, `cursor-self-test`, `terminal-self-test`, `preferred-terminal-self-test`, `uniform-sample-self-test`, `traced-path-self-test`, `moving-self-test`, `return-self-test`, each with a fresh directory |

The preferred-terminal and traced-path modes currently stop at
`uniform source does not carry edge; retained moving retry required`.
The checkpoint retains attempted operands in `inconclusive-uniform.json`.
These two existing failures and their unresolved moving fallback are preserved
in the current harness; report their results separately from passing modes.

`check-prepared-projections.sh --models` checks both projection sources
through complete C output and C compilation. It requires the owner C artifacts
to be current from the preceding warning-fatal build; stale/missing artifacts
fail rather than launching redundant export-info jobs. The remaining declared diagnostics/benchmarks retain
their CLI contracts and full proof/build coverage; they are not facade imports.
