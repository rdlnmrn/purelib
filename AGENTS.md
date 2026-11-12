# Repository agent instructions

## Modules, visibility and placement

- Use Lean's explicit module system: start new Lean sources with `module`.
  Keep declarations private by default; make only the API needed by real
  clients public. Use `public section` only for a coherent public group.
  Decide name visibility, body exposure, import re-export and execution phase
  separately. Expose definition bodies only where client reduction requires
  it; keep proof implementations private and preserve intended opacity.
  Before changing public exposure, native bindings or tool-module phases, read
  [module interfaces](docs/lean-development.md#module-interfaces-and-execution-phases).
- Prefer ordinary `import`. Use `public import` only for a deliberate API
  re-export, such as a facade or a required existing public contract.
  Public signatures and exposed bodies, including retained proof fields, need
  public access to their owners. Incidental transitive availability is not an
  API contract: give callers direct imports for the dependencies they use.
  Verify the retained public path in the same execution phase; do not duplicate
  an existing deliberate re-export.
  Proof tactics and elaborator helpers are normally ordinary or `meta` imports.
  Preserve synthesized instances when narrowing imports; successful compilation
  alone does not establish the same elaboration.
  When changing instance priorities, check retained operations and local
  precedence; follow the module-interface guide for preservation comparisons.
  Use `import all` only when a client must reduce a private body; record the
  owner and reason. Do not bypass visibility with backward compatibility
  options or raw compiler-private names.
- Reusable sources belong under `Purelib/` and `Purelib.*`; regressions under
  `TestPurelib/` and `TestPurelib.*`. Keep publication chapters, optional examples, generated
  fixtures in their established homes and build targets.
  Keep regressions reachable from `TestPurelib.All` or a standalone executable;
  run `scripts/check-purelib-surfaces.py` when adding regression modules.
  For interim checkpoints, use an existing standalone target for the subject
  when available; aggregate facade builds can pull in unrelated import closures.
  Group examples by their mathematical subjects, not the review or migration
  that produced them; retain examples that demonstrate real construction chains.
  Examples own their demonstrated constructions; regressions consume those
  constructions and keep exhaustive behavior checks under `TestPurelib/`.
  Library, example and publication modules must not depend on regression modules.
  Reusable library facades must not pull in publication chapters or optional
  fixtures. Do not recreate retired source roots or forwarding modules.
  Publication coverage requires listed claims to remain publicly reachable
  from their promised facade; check current owners and consumer-phase re-exports.
  Check an intended new source path for existing contents before creating it.
- Place declarations by the mathematical objects and operations they concern,
  not their current caller or the theorem that motivated them.
  General mathematics needs no second consumer to belong with its subject.
  Representation-specific applications belong with that subject's realization
  family; intrinsic CCL representation operations belong in `Purelib.Data.CCL`.
- Group modules around actual objects and dependency chains. Keep construction,
  refinement, readback and comparison operations discoverable in the object's
  namespace. Avoid catch-all contexts, suffix-based collections and unnecessary
  one-definition files. Name mathematical objects and directional operations;
  omit redundant `Finite`/`Constructive` qualifiers.
- Declare groups inside their actual owner namespace, normally matching the
  source module, and use short declaration names and references within it.
  Do not retain a foreign wrapper and root each declaration back to its owner.
  Consolidate redundant namespace/section wrappers after checking their variables,
  options, local instances and scoped registrations. Do not introduce authored namespace
  components beginning with an underscore: reuse the original owner for aliases,
  or give a distinct mathematical object its own name. Compiler-generated
  private/hygiene names and `_root_` are outside this naming rule.
  Before moving declarations or changing scope boundaries, read
  [namespaces and source moves](docs/lean-development.md#namespaces-openings-and-source-moves).
- Prefer opening a parent namespace and retaining a short namespace qualifier,
  such as `Matrix.determinant`. One alias for a type/namespace is fine when it
  disambiguates related objects (`Matrix2.determinant`); do not rename its
  functions individually or invent prefixed names such as `matrix2_determinant`.
  Share dependency openings across the file or a coherent group. Use short
  qualifiers for collisions and reserve local openings for isolated uses.
  Preserve name resolution, implicit parameters and selected instances.
  Reserve fully qualified references for unavoidable disambiguation, recursive
  name resolution or preserving compiler-retained syntax.
  Follow [namespace linting](docs/linting.md#repeated-namespace-prefixes) for
  reported long routes; preserve compiler-retained notation expansions.
- Keep imports narrow and the module graph acyclic. Do not impose namespace
  allowlists or mandatory core/adapter barriers. Constructive proof restrictions
  and publication coverage remain required.
- Document source declarations, including structures, definitions and theorems.
  One summary sentence suffices for a trivial declaration. For nontrivial
  declarations, follow the summary with a blank line and a short paragraph
  explaining the object, operation or claim and its essential conditions.
  Describe the declaration itself, not an intended application, current caller
  or motivating theorem.
- Keep blank separators empty and use at most two consecutive newline characters
  in Lean sources. Preserve whitespace inside string literals.

## Constructive proofs and dependencies

- Apply mathematical restrictions to admitted constructions and their complete
  retained proof and execution dependencies. Untrusted generators, tactics,
  exporters and helper scripts may use broader host facilities when their
  outputs are checked under the admitted rules for the intended claim and inputs.
  A helper used by the resulting construction is still a dependency; a helper
  whose unchecked verdict is trusted is part of verification. Names, locations
  and meta labels do not establish either exemption.
- Before presenting foundation-policy choices or their consequences, inspect
  the pinned Lean rules and implementations. Distinguish source notation from
  elaborated constructions, generated helpers and retained dependencies; check
  existing finite specializations before proposing exclusions.
- Retain Lean's impredicative `Prop` for the current finite-construction work.
  Impredicativity removal and generation-based propositional layering are
  deferred.
- Construction-policy enforcement belongs in the repository's axiom-checking
  workflow, with an extensible whitelist of construction rules and checked side
  conditions.
  Preserve explicit module/file scopes and complete mathematical
  dependency checks. Unknown cases prevent a certified pass; add justified rules
  rather than namespace exemptions. Use scoped check-then-lint edit verification
  during branch work and full coverage before integration into `master`.
  Finite child domains beyond `Fin n` retain executable original-index
  enumerations with checked exhaustive coverage, together with an admitted
  finite whole construction. Reuse existing owners and coverage laws; an erased
  existence or finiteness claim does not supply the required enumeration data.
- No `noncomputable`, `classical`, choice-based shortcuts or choice-derived
  enumeration such as `Fintype.ofFinite`. Retain executable finite constructions.
  Prefer direct proofs with explicit witnesses; use contradiction only for
  negative goals or when no comparably clear constructive proof is available.
- Audit Mathlib declarations, instances and transitive proof/import dependencies,
  not just statements or module names. Do not import or use infinity-dependent
  routes: infinite carriers/cardinality arguments, completed infinite objects,
  compactness, completion or infinite series. Finite fields are the explicit
  exception when carrier, enumeration, decidability and witnesses are executable
  data; this does not relax the choice restrictions. Use the narrowest audited
  finite algebraic dependencies.
- Do not introduce new `implemented_by` uses, including programmatic replacement
  registrations. Existing project and upstream uses are permitted; removing them
  is not a prerequisite for unrelated work. Require admitted finite termination
  arguments and callback contracts, without a separate execution-step bound
  unless the API explicitly promises a computational budget.
- Admit selected standard runtime primitives under an explicit execution-trust
  assumption: identify their admitted finite logical definitions, actual pinned
  native implementations and input/result/callback contracts. Inspect before
  admission; Core origin alone is insufficient. Native correctness and
  termination under those contracts are trusted, without requiring a formal C
  correspondence proof. Keep callback and mathematical-evidence checks and the
  restriction on new `implemented_by` uses. Project-added `extern` bindings and
  implementations and their correspondence-evidence policy are deferred pending helper cleanup
  and an actual surviving certified use; no blanket exemption follows from this rule.
- Keep source-facing mathematical declarations and their complete transitive
  dependencies axiom-free, including private and generated proof dependencies.
  The authoritative checker's normal mode selects safe non-meta source-facing
  declarations and registered compiler rewrites. Logical closure auditing alone
  does not audit actual native implementation behavior.
  Use `--all-helpers` to audit every retained kernel declaration when that strict
  scope is requested.
  Internal producer-helper audits are optional diagnostics, not a requirement
  that an untrusted producer itself satisfy the mathematical restrictions.
  Retain complete mathematical output-closure checks. IR-only inventory is an optional
  diagnostic report and establishes no kernel proof or axiom-freedom claim.
- Prefer direct proofs or kernel `decide`. Do not introduce `native_decide`
  proofs or axioms. Before writing or changing proof routes, read
  [constructive proof techniques](docs/lean-development.md#constructive-proof-techniques).
  Audit retained dependencies, including implicit indexing proofs, tactic
  auxiliaries and simplifier companions; source syntax alone is insufficient.
- Import `Purelib.Tactic.QuotientFreeOmega` directly for `omega0` and for
  `omega` proofs using this repository's quotient-free frontend. Preserve the
  original frontend when narrowing imports, including automatic index-bound
  proofs. Audit an existing proof route before replacing it.
- Prefer structural recursion. Supply constructive decrease proofs for necessary
  well-founded recursion and audit generated auxiliaries. Preserve clients'
  actual unfolding and simplification when changing executable definitions.

## Owned data and public APIs

- Separate stable mathematical owners, requests, retained realizations,
  comparison certificates and execution outcomes. Reuse original nominal
  parents and correctness-bearing indices/bounds; do not replace them with
  runtime IDs, copied fields or convenient new owners. Small certified views
  and exact reducible aliases may shorten interfaces while preserving parent
  identity, indices and defining equations.
- Before adding a record or certificate family, compare its fields and
  invariants with the nearest existing owners. Reuse their constructors,
  containers and laws; justify a new type by its distinct invariant, retained
  cache or ownership boundary. For alternate interpreters, replay views and
  query constructions of the same operation, share branch logic and derive
  the views from it. Verify complete values, ordered traces, failures, fuel
  accounting and cache reuse when consolidating execution.
- Cache expensive executable data with specification equalities/certificates.
  Builders and downstream code must consume those exact caches; readback
  equality alone does not establish execution reuse. Retain factors outside
  entry-producing functions and pass retained tails with their original-tail
  identities instead of recomputing them.
- Keep exact readback, refinement, operational agreement, quantitative comparison,
  geometric correspondence and replay agreement distinct. A comparison retains
  both input owners, its actual relation witness, residual, bound and request
  payment. Choosing, payment and readback use the same retained observations
  and summaries. A successful common owner does not replace the inputs. Preserve
  ordered signed occurrences, source/chart witnesses, coefficient factors,
  constants, stage floors and distinct paired/conjugate/magnitude data.
  Compose bounds according to the actual quantity; inequalities over unrelated
  readings do not establish a domain relation.
- Public checking/preparation APIs return typed certificates of success,
  invalidity/obstruction or an inconclusive finite attempt. Invalidity identifies
  and proves the violated condition. Inconclusivity retains attempted data,
  all unresolved cases/obligations, computed bounds, budget/depth and stopping
  reason, with proofs linking them to the actual procedure. Reuse cached work.
  A failed attempt or timeout proves no global pole, divergence or impossibility.
  Booleans may be internal helpers, not the sole public explanation.
- Provide named constructors, projections and transports so production clients
  can complete a construction without rebuilding records or re-proving ownership.
  State source/target, extra evidence, retained/computed data and guarantees.
  Introduce shared abstractions only for demonstrated contracts, normally with
  two real consumers; add composition/reversal operations only with needed laws.
  Explain the object, invariants and construction chain near its owner using
  actual APIs. Avoid speculative metadata or tracing frameworks.

## Changes and consumer migration

- Replace APIs atomically across all consumers, including `scripts/`, generator
  templates, tests, optional examples and publication/build tooling. Remove
  unused implementations and compatibility wrappers. Report blocked consumers
  and reasons explicitly. Preserve existing public contracts, executable bodies,
  fields, selected witnesses and failure semantics unless the task authorizes
  changing them; placement work is not algorithm-replacement authorization.
- When a client outside a module needs a private declaration, expose the needed
  original declaration under its mathematical name, preserving its body and
  dependent identities. Do not create duplicate public copies or names with a
  `_public` suffix.
- Before adding or exposing a theorem, check existing owners for the same
  claim. Check relevant active branches and handoffs when work overlaps;
  pin revisions when comparing or reusing that work. Reuse or generalize owners;
  do not develop parallel proofs or certificate families for the same contract.
- Choose verification to match the promised preservation contract. Ordinary
  maintenance needs affected-consumer builds and applicable audits. Exhaustive
  reference inventories and literal compiled-record comparisons are required
  when the task promises those stronger guarantees; follow
  [source migration](docs/lean-development.md#namespaces-openings-and-source-moves)
  and [compiled comparisons](docs/compiled-tracing.md#choosing-a-comparison-contract).

## Documentation upkeep

- Keep documentation focused on current contracts, usage and remaining work.
  Delete fully implemented plans and remove their completed sections from
  `docs/ideas.md`, `docs/future.md` and other roadmaps; repair incoming links.
  Preserve useful API guidance in subject guides, not completion ledgers.
  Extend the existing subject guide instead of adding one guide per checkpoint,
  fixture or implementation step; keep detailed declaration contracts in source.
- Keep technique guides reusable and procedural. In particular,
  `docs/profiling.md` covers diagnosing and fixing slow module builds: extract
  the symptom, cause and repair. Omit chronological investigations, historical
  benchmark tables, temporary paths, process IDs and receipt inventories.
- Leave routine verification outcomes in CI and run artifacts. Do not add
  "all verification gates passed" claims, audit counts, build/LSP inventories
  or stale pending-check notes to README files or documentation. Keep check
  instructions and substantive unresolved limitations.

## Generators and build performance

- Give reusable modules one Lake library owner. Checkpoint libraries declare
  their script roots and obtain reusable modules by import; overlapping roots
  can make native library emission cyclic even when source imports are acyclic.
  Retain directories used by Lake namespace globs in Git, even when they have
  no Lean sources. Verify a full build after adding a glob; scoped targets may
  never visit it.
- Prefer executable library constructions and compact generic proofs to large
  precomputed certificates. Do not add bespoke certificate-search harnesses or
  check in their certificate/proof dumps to make ordinary library proofs build.
  Use existing automation, scalar readbacks, schema lemmas and
  kernel decision on small finite goals. Keep expensive numerical and replay
  outputs in ignored worktree-local stores; reusable APIs must not depend on
  a particular harness run.
- Prefer direct Lean regressions with fixed inputs and explicit finite budgets;
  test invalid records through library APIs. Do not add serialization formats,
  persistent fixture stores or restart machinery solely to support tests.
  Persistence infrastructure needs a demonstrated consumer outside test
  scaffolding, such as a numerical tool or verification cache. Test that
  consumer's actual reload/rejection contract through existing runners.
  Preserve expected failure and inconclusivity; do not change inputs or
  escalate budgets until a certificate appears.
- Size numerical demonstrations to exhibit the theorem's construction and
  certificates. Use small inputs and coarse accuracy sufficient for that
  purpose; stop once the required construction and certificate checks succeed.
  Keep higher precision and stress trajectories optional. General proofs
  establish the theorem's full range independently of those runs.
- Use deterministic generators in `scripts/` when fixed finite witness data is
  itself required by a real client. Keep outputs compact and coefficient
  selection in one source of truth, with reproducibility/check mode. Producers
  are untrusted: verify generated data with exact kernel-checked predicates or
  proof-producing verifiers.
- Keep generated proofs as compact schema applications or readable constructor
  proofs. Check a source-size budget before expanding a family; do not dump
  elaborated expressions into source or duplicate them in manifests.
- Constructor injectivity certificates should be derived from the datatype's
  metadata through `constructive_injectivity TypeName`, rather than maintained
  field recipes or serialized proof terms. Check generated mathematical proof
  closures through the normal authoritative audit; the generator's independent
  internal helpers need not be axiom-free; see
  [constructor certificates](docs/constructor-certificates.md). Before changing
  shared certificate reconstruction, read the
  [proof-generator procedure](docs/lean-development.md#proof-generators).
- Reuse completed expensive work through atomic incremental checkpoints and
  checked reloads in durable worktree-local stores. Preserve compatible
  artifacts, bind actual inputs and outputs, and test interrupted-run recovery.
  Bind the environment actually passed to workers; keep per-launch diagnostic
  IDs and pool scheduling settings in their supervisors.
  Before implementing or changing resumable jobs, read
  [checkpoint guidance](docs/profiling.md#reuse-completed-work-not-just-logs).
- Before replacing a worker job, stop its supervisor and descendants after
  checking their process identities. Preserve checkpoints and confirm that no
  superseded worker remains live; detached workers can outlive their supervisor.
- Keep ordinary Lean limits: do not add `maxRecDepth` or `maxHeartbeats` overrides
  to sources, or weaken watchdogs to force success. Diagnose the expensive phase
  before changing proofs; use the [profiling guide](docs/profiling.md) for
  dependent signatures, generated helpers, reduction and emission costs.
- Size host-audit pools from measured whole-worker RSS and available memory;
  duplicated transitive imports dominate memory. Budget subagents separately
  and monitor only owned tool process groups; preserve proof scope and limits.
- Check complete artifact/code emission early for dependent interfaces and
  executable builders; declaration checking alone is insufficient. Apply the
  master integration timing policy below. After changing exposure, inlining or
  dependent type boundaries, check affected production consumers as well as the
  owner: a faster owner alone does not establish a successful repair. Consult and update
  [profiling.md](docs/profiling.md) for new bottlenecks and repairs.

## Verification and working practice

- Always work on a topic branch rather than `master` or a detached HEAD, unless
  the user explicitly grants an exception. Continue existing tasks in their
  current worktrees, including legacy locations; no relocation is required.
  For new tasks, use the worktree helper below to create a fresh worktree on a
  topic branch before editing. Preserve existing work. Agents own commit timing:
  make coherent checkpoint commits as work
  progresses and commit finished changes without asking for routine confirmation.
  Keep work on its branch until integration is explicitly requested.
- Preserve pre-existing user and agent changes. Stage and commit only changes
  belonging to the task; do not absorb unrelated work or discard it during
  cleanup. Inspect child worktrees for uncommitted work before removing them.
- Keep tracked PDFs consistent with their current TeX sources. After changing
  a manuscript or any shared TeX input, regenerate every affected PDF and include
  it in the same commit; never commit manuscript edits with stale PDFs.
  Use `scripts/build-papers.sh` for the four main papers and the manuscript's
  established build command for other publications. Shared CCL source changes
  require rebuilding both CCL PDFs. Check that PDF generation succeeds before
  declaring manuscript work complete.
- During branch work, incrementally build, axiom-check and lint changed Lean
  modules and affected consumers after meaningful edit batches and before
  checkpoint commits. Use warning-fatal builds
  (`scripts/run-lake.sh --wfail build <targets>`), scoped
  `scripts/check-axioms.sh <targets>` and scoped
  `scripts/run-lake.sh --wfail lint <modules>`. Run Lake through
  `scripts/run-lake.sh` to select the checked patched toolchain and serialize
  native-provider preparation. No linter warnings may remain.
  Reserve full integration gates, including nanoda, for merge readiness;
  track accumulated changes and affected consumer coverage.
- Nanoda is required when ready to merge into `master`, not for routine branch
  work, checkpoint commits or branch implementation completion. Run it earlier
  only when explicitly requested or needed for a specific diagnosis. A branch
  completion report must distinguish implemented work, incremental checks and
  the integration checks still pending.
- Branch work may be committed and declared complete with known module timing
  overruns. Report the affected modules, measured times, checks blocked by
  performance and remaining optimization; do not call a failed or incomplete
  check a pass. Performance debt does not waive mathematical correctness,
  warning-fatal builds or the applicable verification requirements. Keep
  unrelated performance cleanup outside the requested task.
  Before merging or otherwise integrating Lean changes into `master`, changed
  project modules and consumers affected by the changes must compile in under
  30 seconds with current dependencies and complete artifact/code emission.
  Each project-owned nanoda check in that affected scope must also finish in
  under 30 seconds. An unchanged
  source can become slower through changed dependencies, exposure, inlining or
  instances. Do not require profiling or cleanup of unaffected modules.
  Cached builds do not establish fresh compilation time. Use controlled timings
  and disclose observed unrelated overruns without expanding the task to fix them.
  These performance targets exclude third-party code, including the pinned Lean
  toolchain. See [verification.md](docs/verification.md) for current enforcement.
- When integration is authorized, prepare the candidate tree on a topic branch
  and check it against current `master` before advancing `master`. For a local
  merge, use `git merge --no-ff --no-commit <topic>` so fast-forwarding cannot
  bypass the checks. Build, fix affected slow modules and run applicable final
  gates before committing the merge. Keep fixes on the topic branch where
  practical. Follow the [integration procedure](docs/verification.md#preparing-an-integration).
- Start every module build and regression test under a suitable watchdog.
  Use `scripts/run-lake.sh` for Lean compilation and the supervised checkers or
  equivalent owned-process supervision for standalone regressions. A caller's
  short tool wait is not a watchdog; see [watchdogs](docs/verification.md#watchdogs-and-process-ownership).
  On every branch, terminate an individual module build at two minutes and a
  regression test at five minutes. Send SIGKILL after a fifteen-second grace
  if needed. Investigate the overrun immediately, before retrying or continuing
  dependent work. An explicit user-authorized release exception may select
  `CCL_MODULE_TIMEOUT_SECONDS` up to 300 for guarded builds; record that budget
  and retain the ordinary default otherwise. A separately authorized tooling-test
  exception may use `CCL_TOOLING_TIMEOUT_OVERRIDES` for exact discovered case IDs,
  with a maximum of 600 seconds and the selected deadline bound to each receipt.
  Do not increase a deadline automatically
  after failures. Finishing
  before termination does not establish master readiness. Avoid blind retries
  after an overrun; bounded profiling, controlled timing comparisons and required
  verification are valid reasons to rerun unchanged code. Reuse completed work.
  Full builds, test suites, lint, axiom checks and full nanoda runs may take
  longer than five minutes in aggregate. Keep progress reporting and supervision
  active throughout; aggregate duration is not a module measurement.
  Numerical computations, harnesses and generator jobs retain the five-minute
  limit and fifteen-second grace. Use checked incremental checkpoints for
  useful bounded batches, preserving the mathematical requests and budgets.
  Preserve completed artifacts and verify the owned supervisor and descendants
  have exited before restarting.
- Keep every declared library/executable in `defaultTargets` and preserve the
  selected native linter providers for Core-only sources. Before changing lint
  configuration or coverage, read [linting.md](docs/linting.md).
- `scripts/check-axioms.sh` is authoritative. During branch work, including
  before commits, scope audits to changed Lean modules (module names or `.lean`
  paths). Do not treat known correctness failures as completed work; distinguish
  them from pending checks and the performance debt permitted above.
  Validate generated target lists before execution; missing or empty scoped
  inventories must fail instead of selecting the default full scope.
- Before integrating mathematical Lean changes into `master`, including changes
  to generators of mathematical Lean sources, run the full integration gates through
  `scripts/check-all.sh`; see [integration checks](docs/verification.md) for
  coverage, caches and prerequisites. These gates normally require a successful full build
  (`scripts/run-lake.sh --wfail build`), full lint
  (`scripts/run-lake.sh --wfail lint`), full axiom audit
  (`scripts/check-axioms.sh --configured-scripts --full`) and full nanoda pass
  (`scripts/check-nanoda.sh`) on the final tree, including affected optional
  targets. Incremental branch checks do not replace these merge-readiness gates.
  Do not run the full suite merely to complete ordinary branch work. Changes confined
  to linting or nanoda-checker tooling, including its Lean support code and
  generators, are exempt from the axiom and nanoda gates; run focused tooling
  regressions and appropriate builds. Script changes that neither change
  mathematical Lean sources nor generate them require relevant tooling tests
  and build checks, but no axiom audit or nanoda pass.
  Documentation-only changes require no Lean build or proof audit.
- Serialize builds and Lean checks that import their outputs in the same
  worktree. Lake can replace artifact parts during emission; overlapping
  writers or readers can observe missing or stale parts.
  Give independent agent compilers stable artifact snapshots and separate
  outputs; final builds and audits must still use the current working tree.
  Freeze Lean source edits before an authoritative audit: its required
  support/regression build can rebuild beyond the named audit modules.
- Before using LSP queries for migration evidence, follow the checked
  [frontend alignment](docs/profiling.md#align-lsp-workers-with-the-checked-native-frontend)
  and [reference procedure](docs/profiling.md#lsp-with-the-private-core-prefix).
- Create worktrees for new tasks, and any additional worktrees used by subagents,
  inside the task's original top-level worktree. Existing tasks continue where
  they are already working. Use
  `python3 scripts/worktrees.py create TOPIC` to create `.worktrees/<topic-slug>/`
  on its matching branch, and `list` to inspect the current Git inventory.
  Pass the original root to subagents; use `--root ORIGINAL_ROOT` when needed.
  Moving into a child does not redefine that root. Do not repurpose an old task
  directory for another subject or create sibling worktrees under `~/repos`
  or temporary directories. Use `retire TOPIC` for completed, merged worktrees;
  it retains branches and archives ignored data. Follow the
  [worktree procedure](scripts/README.md#task-worktrees), including its process-use
  checks. Keep `.worktrees/` ignored and excluded from parent source inventories.
- Inspect live build/check output for progress and diagnosis, with or without
  subagents. Preserve the owning wait, raw exit and required receipts; partial
  output or a worker's success does not establish success for the complete run.
- For progressive GitHub releases, reuse the topic worktree in Git configuration
  `ccl.releaseWorktree`; keep its path and caches after publication. Use the durable
  `ccl.publicHistoryStore` for mapping backups and receipts, and verify mounted
  storage before writing. Follow [release storage](docs/verification.md#durable-release-checkpoints).
- `--no-build` requires current selected, private and audit-support artifacts;
  follow [artifact currentness](docs/verification.md#artifact-currentness-and-audit-coverage).
  Diagnose reported audit failures through `scripts/trace-axiom.sh`, following
  [compiled tracing](docs/compiled-tracing.md); do not create ad-hoc `#print axioms`
  probe files.
- Update AGENTS.md when new rules prove helpful. Keep it concise and actionable:
  consolidate related guidance and remove superseded rules.
- Give concrete progress updates roughly every 60 seconds: findings, remaining
  uncertainty and the next question to resolve. Explain changes of approach.
