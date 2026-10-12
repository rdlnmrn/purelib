# Lean linting

The project uses Lean 4.32.2's built-in lint runner (`builtinLint = true`)
with explicit options and native linter providers in `lakefile.toml`.
The selected syntax checks run in every project build, including Core-only
sources. The native providers load the pinned Mathlib linter implementations
without adding Mathlib or Batteries imports to the sources being checked.
There is no new dependency or separate Batteries lint driver.

## Configuration

Use Lake's option-record form when configuring an option and its suboptions:

```toml
leanOptions = [
  { name = "weak.linter.style.longLine", value = true },
  { name = "weak.linter.style.longLine.maxLineLength", value = 120 },
]
```

Lake decodes each `name` string as a hierarchical Lean name. A table with
unquoted dotted keys cannot hold both `longLine = true` and
`longLine.maxLineLength = 120`: TOML would need `longLine` to be both a Boolean
and a table. Quoting a whole dotted table key instead creates a single Lean
name component, which does not select the intended option.

Weak options support Lean's `set_option` mechanism and apply to project
sources without changing dependency-package settings. Any necessary exception
must have a concrete reason and the narrowest useful scope; do not use
`lake lint --record-exceptions` to generate blanket suppressions.

The package `dynlibs`/`plugins` settings load the required native dependencies
and reviewed syntax-linter providers in dependency order. Setting options alone
would not register Mathlib linters in Core-only files. Keep that provider order
consistent with the pinned dependency sources and rerun the Core-only fixtures
after changing providers or the dependency revision. Imported providers can
register additional checks, but we do not enable a blanket Mathlib linter set.

The wrapper builds these native providers sequentially before project builds
and lint runs. Lake 4.32.2 can otherwise schedule multiple writers for a cold
shared dependency when resolving several plugin facets concurrently. Preparation
uses the dependency packages' own settings and Lake's incremental traces; the
project compilation then runs with the complete selected linter configuration.
Unrelated commands, alternate workspace/configuration arguments and `--no-build`
do not prepare providers.

## Selected checks

Every check below is explicitly enabled, including useful checks that already
default to true when their provider is loaded.

| Option | Diagnostic |
| --- | --- |
| `linter.unusedVariables` | Unused variables in supported terms and patterns. |
| `linter.unusedSectionVars` | Unused section variables retained as declaration parameters. |
| `linter.missingDocs` | Missing documentation on supported public declarations; skips private declarations and ordinary theorems. |
| `linter.unusedTactic` | Tactic calls that make no change, with exclusions for intentional assertions and control tactics. |
| `linter.dupNamespace` | Repeated components in declaration names. |
| `linter.style.nativeDecide` | Use of `native_decide`, which the project prohibits. |
| `linter.style.openClassical` | Unscoped `open Classical` or `open scoped Classical`. |
| `linter.style.maxHeartbeats` | Local heartbeat changes without an explanatory comment. |
| `linter.style.longLine` | Lines exceeding the configured **120-character** limit; import lines and lines containing URLs are exempt. |
| `linter.style.whitespace` | Declaration-header spacing and command placement. |
| `linter.style.docString` | Docstring formatting. |
| `linter.style.docString.empty` | Empty docstrings. |
| `linter.style.setOption` | Debugging options left in source and selected problematic option settings. |
| `linter.style.nameCheck` | Double underscores in declaration names. |

The first three are Core checks. The other checks run through the native
providers even when a source has no direct or transitive Mathlib import.

`linter.unusedDecidableInType` and `linter.unusedFintypeInType` are explicitly
**disabled**. Their suggested repairs use `classical` or replace executable
`Fintype` data with `Finite` and `Fintype.ofFinite`, contrary to this project's
constructive rules. Retain explicit decidability and executable enumeration.

The constructive source rules remain stricter than the style checks:
`openClassical` allows declaration-local openings and does not reject the
`classical` tactic; `maxHeartbeats` accepts documented local changes and does
not prohibit `maxRecDepth`. Documentation checks do not enforce our requirement
to document every theorem and private declaration. Keep the authoritative axiom
audit and nanoda checks; linting does not replace them.

## Running and coverage

```sh
scripts/run-lake.sh --wfail build
scripts/run-lake.sh --wfail lint
scripts/run-lake.sh --wfail build Purelib.Data.Vector.Basic
scripts/run-lake.sh --wfail lint Purelib.Data.Vector.Basic
scripts/run-lake.sh --no-build --wfail lint Purelib.Data.Vector.Basic
scripts/run-lake.sh check-lint
python3 -m scripts.test.linting.test_configuration
python3 -m scripts.test.linting.test_runner
```

All declared libraries and executables are default build targets, including
examples, regressions, publications and configured harness/checkpoint owners.
Builds compile executables; they do not run the harnesses. Keep `defaultTargets`
complete when adding a target. Explicit build targets remain scoped.

An unscoped `run-lake.sh lint` selects the authoritative active-source inventory
from `project-modules.py --configured-scripts`, including all Purelib sources,
examples, regressions, publications and configured script owners. Discovery errors, empty inventories and duplicate module names fail
instead of falling back to Lake's default lint roots. Explicit module lists
remain scoped; arguments following `--` keep their driver-argument meaning.
Plain `lake lint` still uses Lake's default target roots, so use the wrapper for
complete lint coverage. CI uses the wrapper as well.

For ordinary lint invocations, the wrapper builds the selected modules once,
then runs the unchanged `Lake.BuiltinLint.run` on one module per native process.
The small launcher is compiled once and reused with checked compiler, helper,
import and executable bindings. It includes interpreter support and full module
initialization so imported meta linters and extensions still run. Process exit
releases imported data instead of accumulating it over a large selection.

`CCL_LINT_JOBS` defaults to `auto`: use the CPU affinity available to the process,
limited by Linux's available-memory reading at two GiB per worker (the previous
full pass measured a peak of 1.87 GiB). Without a memory reading, auto mode falls
back to at most eight workers. Set a positive integer to choose the concurrency
explicitly; there is no fixed core or worker cap, apart from the selected module
count. Account for other active checks when choosing an explicit count.

```sh
CCL_LINT_JOBS=auto scripts/run-lake.sh --wfail lint
CCL_LINT_JOBS=192 scripts/run-lake.sh --no-build --wfail lint
```

The scheduler keeps one outstanding job per worker and reports completions as
they arrive. Setup and checker timings distinguish preparation from lint work.
With `--no-build`, the same official Lake step checks artifact currentness without
emitting artifacts; missing or stale inputs fail before checker workers start.

Successful results are saved atomically under `.lake/builtin-lint`. Reuse checks
the selected module's complete compiled import closure, private/server/IR parts,
source, compiler and native libraries, helper, options and saved output digest.
Completed successes are checkpointed in batches, checking the union of their
import closures once instead of checking shared file signatures for every module.
A batch is published when it reaches the worker count or after approximately one second,
including while other workers are slow. Interrupted runs retain published
checkpoints; an unpublished batch and failed checks are rerun. Custom
lint flags or drivers and alternate workspace/configuration arguments keep
Lake's original dispatch and memory behavior.

`check-lint` checks runner configuration, not option validity or source
compliance. The focused tests verify actual diagnostics on Core-only sources,
the 120/121-character boundary, unchanged compiled import boundaries, default
source ownership and explicit scope preservation. Native-launcher fixtures
compare exit codes and full checker output with the original interpreted checker
for a clean module, a saved text warning and an interpreted meta environment
linter. The native providers must have been built first; any focused project
build builds them as dependencies.

The warning-fatal full build enforces the selected syntax linters across all
default targets. Run it together with the all-source lint command above when
changing sources or linter configuration; passing the configuration fixtures
alone does not establish repository compliance.

The built-in environment pass reads exported module data; it is not a
private-body audit and does not run Batteries' separate `@[env_linter]` checks.

## Conventions left opt-in

We do not enable `linter.mathlibStandardSet` or `linter.all` wholesale.
Remaining optional conventions include:

- Copyright/license/author headers and module docstrings.
- A file-length limit; line length is configured separately at 120 characters.
- Preferred `fun`/`λ`, `<|`/`$` and tactic-focus spelling, blank-line rules,
  preferred tactic syntax and restrictions on tactic sequences.
- Explicit `end` commands for file-wide public sections (`missingEnd`).
- Warnings about modules with only private declarations (`privateModule`),
  which conflict with deliberate implementation and regression modules.
- Batteries' theorem-documentation and underscore-in-definition-name checks.

Import minimization remains informational. Before removing imports, check
retained public paths, execution phases, synthesized instances and proof routes
as required by `AGENTS.md`; a successful build alone is insufficient.
