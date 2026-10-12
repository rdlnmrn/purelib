# Repository agent instructions

## Modules, visibility and placement

- Use Lean's explicit module system: start new Lean sources with `module`.
  Keep declarations private by default; make only the API needed by real
  clients public. Use `public section` only for a coherent public group.
  Decide name visibility, body exposure, import re-export and execution phase
  separately. Expose definition bodies only where client reduction requires
  it; keep proof implementations private and preserve intended opacity.
  Put `public section` before its named namespace, or close the section before
  closing that namespace. Public abbreviations and instances already expose
  their bodies; do not add redundant `@[expose]` attributes.
  When clients must reduce a derived equality procedure, use
  `deriving @[expose] DecidableEq` to expose its original generated helpers.
  Exposure must be set at declaration time, not with a later attribute.
  In an entirely meta tool module, preserve that phase for generated recursors,
  projections and match helpers too: `meta section` does not tag every auxiliary.
  Check persisted phase metadata and report the strict helper closure separately.
- Prefer ordinary `import`. Use `public import` only for a deliberate API
  re-export, such as a facade or a required existing public contract.
  Public signatures and exposed bodies, including retained proof fields, need
  public access to their owners. Incidental transitive availability is not an
  API contract: give callers direct imports for the dependencies they use.
  Keep those direct imports ordinary when another deliberate public dependency
  already re-exports the owner. Verify the retained public path in the same
  execution phase; do not duplicate its re-export.
  Proof tactics and elaborator helpers are normally ordinary or `meta` imports.
  Preserve synthesized instances when narrowing imports; successful compilation
  alone does not establish the same elaboration.
  Keep scoped and global registrations of the same instance at the same
  priority: activating a scope replaces that instance's global entry.
  Before changing data-instance priorities, verify complete retained operation
  records/functions and direct local instance precedence by kernel comparison.
  Use `import all` only when a client must reduce a private body; record the
  owner and reason. Do not bypass visibility with backward compatibility
  options or raw compiler-private names.
- Reusable sources belong under `Purelib/` and `Purelib.*`; regressions under
  `Test/` and `Test.*`. Keep publication chapters, optional examples, generated
  fixtures in their established homes and build targets.
  Group examples by their mathematical subjects, not the review or migration
  that produced them; retain examples that demonstrate real construction chains.
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
  Absolute `_root_` qualification applies to declaration names, not ordinary
  namespace commands: `namespace _root_.X` creates literal nested components.
  Balance the enclosing scopes before opening an actual top-level owner, and
  retain the variables, options, openings and local instances it needs.
  Closing a namespace deactivates local registrations; keep them in a shared
  enclosing scope, using `with_weak_namespace` when their original declaration
  owner must be retained.
  Namespace ancestry can outrank selectively opened aliases; keep distinguishing
  qualifiers for the original types and instances when moving groups.
- Prefer opening a parent namespace and retaining a short namespace qualifier,
  such as `Matrix.determinant`. One alias for a type/namespace is fine when it
  disambiguates related objects (`Matrix2.determinant`); do not rename its
  functions individually or invent prefixed names such as `matrix2_determinant`.
  Selective `open` and `open ... renaming` require declarations; a namespace-only
  name needs a parent opening and a short qualifier instead.
  Keep namespace routes in selective openings unique across inherited namespaces
  and simple openings: Lean rejects duplicate routes even when they resolve to
  the same declaration. Use a longer parent qualifier when needed.
  Apply this to each dependency actually used; imports alone do not shorten
  references. For repeated long dependency routes, select the needed types or
  open their parent and keep a short distinguishing qualifier. Open dependencies
  once per file, normally inside its main namespace, and let subsequent
  declarations inherit those openings. Avoid
  repeating `open ... in` before individual declarations. Use short qualifiers
  where names collide; reserve local openings for isolated uses or concrete
  name-resolution conflicts. Use a shared section when a coherent group needs
  different opening context, rather than one section per declaration. Preserve
  selected declarations and instances when widening opening scope. Avoid
  openings that shadow existing laws, local names or implicit type parameters.
  Reserve fully qualified references for unavoidable disambiguation, recursive
  name resolution or preserving compiler-retained syntax.
  For same-named Core replacements, select the owned declaration explicitly;
  check its audited route, since literal reduction can pass for either operation.
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
- Keep source-facing mathematical declarations and their complete transitive
  dependencies axiom-free, including private and generated proof dependencies.
  The authoritative checker's normal mode selects safe non-meta source-facing
  declarations and registered compiler rewrites. Use `--all-helpers` to audit
  every retained kernel declaration when that strict scope is requested.
  Strict internal provider-helper auditing remains a separate follow-up; retain
  normal mathematical proof-closure checks. Clean generated
  proofs do not establish a clean generator. IR-only inventory is an optional
  diagnostic report and establishes no kernel proof or axiom-freedom claim.
- Prefer direct proofs or kernel `decide`. Do not introduce `native_decide`
  proofs or axioms. Use the owned `Purelib.Algebra.Ring.IntCast` laws for
  integer casts in generic rings; generic cast lemmas can retain axiom-bearing
  derived negation instances. Avoid deciding large rational comparisons through recursive
  numeral casts: use the owned `natCast_pos_direct` and `natCast_le_direct`
  lemmas with explicit indices. For exact closed computations, rewrite casts
  with `natCast_eq_fromInt` before kernel decision. These reduction costs can
  overflow nanoda even when Lean elaboration succeeds.
  For marked canonical computations, specialize the marker's identity law and
  compose it with retained equalities; implicit conversion can unfold the whole
  computation in nanoda even when Lean checks it quickly.
- Import `Purelib.Tactic.QuotientFreeOmega` directly for `omega0` and for
  `omega` proofs using this repository's quotient-free frontend. Preserve the
  original frontend when narrowing imports, including automatic index-bound
  proofs that invoke Omega without a written tactic call. Check compiled proofs
  against the original source context and run the authoritative audit before
  changing an existing proof route.
- Use the rational `mul_nonneg_direct`, `mul_le_mul_of_nonneg_left_direct` and
  `mul_le_mul_of_nonneg_right_direct` helpers mapped from
  `Purelib.Data.Rat.Fraction.Compatibility`. For mixed strict/weak sum bounds,
  use direct strict translation and `add_le_add_direct`. Generic ordered-ring
  instances and monotonicity can introduce `Classical.choice` and `Quot.sound`.
- Avoid simplification beneath functions/universal binders: it can introduce
  `funext`/`forall_congr`. Specialize quantified facts first. For finite sums,
  use pointwise `sumFin_congr` and scalar transport; a local congruence attribute
  on `Purelib.LinearAlgebra.sumFin_congr` is available. For cached vector
  readbacks, separate definition reduction, `vectorOfFn_apply` rewrites and
  scalar field simplification. In list induction, isolate the current entry
  by scalar congruence before simplifying the unchanged tail.
- When reconstructing generated certificates, match complete applications and
  retain their original argument expressions. Use explicit `mkAppN` arguments
  for nodes containing bound variables; elaborator inference through `mkAppM`
  needs a matching local context. Kernel-check quantified regressions and audit
  the generated auxiliaries after shared reconstruction changes.
- Consume proposition equivalences with `.mp`/`.mpr`. Registering them with
  `simp` can emit proposition-equality companions that retain `propext`.
  For reported scalar `eq_self` routes, exclude `eq_self`/`iff_self` even
  with `simp only`, then finish the remaining equality by `rfl` or direct
  scalar transport. These logical rules are included among the builtins.
- Dependent finite matches can emit logical index-equality proofs independently
  of sparse-match options. Audit their generated auxiliaries and kernel-check
  all-input agreement when changing executable discrimination.
  Prefer structural recursion on direct subterms. For necessary well-founded
  recursion, supply constructive decrease proofs and audit their auxiliaries;
  default termination tactics can retain axiom-bearing simp companions.
  Check existing clients' actual unfolding and simplification after changing
  a selector's definition shape; equal outputs alone do not preserve reduction.
- Split conjunction goals before applying Omega to their scalar components.
  Compound-goal preprocessing can retain a classical proposition decision;
  confirm generated auxiliaries with the authoritative closure audit.
  Clear irrelevant existential assumptions before scalar Omega calls; automatic
  preprocessing can select their witnesses through `Exists.choose`.
- For reflexive comparison goals, use `rewrite` and the owned reflexivity
  lemma; `rw` may close them through imported generic order instances.
- Supply retained bounds explicitly, e.g. `values[index.val]'index.isLt`;
  implicit indexing proofs can introduce Omega and `Quot.sound`. Do not replace
  scalar congruence with `ac_rfl` or structural list identity with blanket
  `List.map_id`; use direct scalar equalities and structural induction.
  Verify proof closures with the authoritative audit, not source-text searches.

## Owned data and public APIs

- Separate stable mathematical owners, requests, retained realizations,
  comparison certificates and execution outcomes. Reuse original nominal
  parents and correctness-bearing indices/bounds; do not replace them with
  runtime IDs, copied fields or convenient new owners. Small certified views
  and exact reducible aliases may shorten interfaces while preserving parent
  identity, indices and defining equations.
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
- When moving an effectful branch into a state action, preserve its enclosing
  early return after running the action. A return inside the action ends only
  that action; check early-return modes through saved artifacts and generator
  markers.
- When a client outside a module needs a private declaration, expose the needed
  original declaration under its mathematical name, preserving its body and
  dependent identities. Do not create duplicate public copies or names with a
  `_public` suffix; `_public` is a terrible naming choice and must not be used.
- Before exposing a private theorem, check for an existing public theorem with
  the same claim and for private declarations with the same qualified name in
  consumers. Inspect the original's complete body even when opaque: public
  elaboration can lose dot access to private companion laws. Expose needed
  originals atomically. Public signatures and exposed bodies need publicly
  accessible certificates; reuse the original mathematical owner where possible.
- Match complete datatype arguments when checking constructor metadata; a command
  for `Parent.Child` does not cover `Parent`.
- Apply declaration routes to references with syntax awareness: preserve record
  field labels, tactics and local identities, and repair method calls after owner
  moves. Follow checked maps rather than mechanical prefix substitution.
  Preserve scoped `variable` binder modes and `include` declarations when moving
  namespace/section boundaries. Identical declaration text does not establish
  the same compiled interface; check existing calls and retained parameters.
  When wrapping Lean, preserve original tactic separators and complete location
  clauses. Keep record continuations inside their fields and use explicit blocks
  for multiline proofs.
- Compiled-record comparisons must retain expression metadata and complete
  `ConstantInfo` fields. A compact expression comparison does not prove literal
  equality. Report source-position relocations separately: bind both sources,
  check token spans (including empty syntax spans), surrounding whitespace and
  anchors, and require every other expression node and record field to agree.

## Generators and build performance

- Give reusable modules one Lake library owner. Checkpoint libraries declare
  their script roots and obtain reusable modules by import; overlapping roots
  can make native library emission cyclic even when source imports are acyclic.
  Retain directories used by Lake namespace globs in Git, even when they have
  no Lean sources. Verify a full build after adding a glob; scoped targets may
  never visit it.
- Produce intricate finite witnesses with deterministic generators in `scripts/`.
  Keep coefficient selection there as the single source of truth and provide
  reproducibility/check mode. Producers are untrusted: verify generated data
  with exact kernel-checked predicates or proof-producing verifiers.
- Keep generated proofs as compact schema applications or readable constructor
  proofs. Check a source-size budget before expanding a family; do not dump
  elaborated expressions into source or duplicate them in manifests.
- Constructor injectivity certificates should be derived from the datatype's
  metadata through `constructive_injectivity TypeName`, rather than maintained
  field recipes or serialized proof terms. Check generated mathematical proof
  closures through the normal authoritative audit; the complete internal helper
  audit remains separate work; see
  [constructor certificates](docs/constructor-certificates.md). Preserve the
  original `.inj` and `.injEq` API; state `.injEq` as an `Iff` without simp
  registration. Suppress default axiom-bearing generation locally when supplying
  checked replacements.
- Expensive generators/harnesses must reuse completed work through atomic
  incremental checkpoints and checked reloads. Preserve compatible artifacts
  and reference shared input manifests through checked receipts instead of
  duplicating them or rewriting the entire aggregate after each batch.
  Test interrupted-run recovery before long reruns. Bind exact request/
  protocol, executable content and retained bytes separately from numerical
  validity and mathematical ownership. Legacy adoption cannot establish
  historical executable provenance. Follow
  [checkpoint guidance](docs/profiling.md#reuse-completed-work-not-just-logs).
- Before replacing a worker job, stop its supervisor and descendants after
  checking their process identities. Preserve checkpoints and confirm that no
  superseded worker remains live; detached workers can outlive their supervisor.
- Keep ordinary Lean limits: do not add `maxRecDepth`, `maxHeartbeats` or external
  resource safeguards to force success. Compact large dependent signatures with
  named `def` aliases for exact propositions and parameter/field types, including
  ownership/bounds. Factor large dependent construction out of recursive
  equations; use scalar lemmas and explicit transport, unfolding only needed
  adapters. Preserve cached data, certificates and equations.
- Size host-audit pools from measured whole-worker RSS and available memory;
  duplicated transitive imports dominate memory. Budget subagents separately
  and monitor only owned tool process groups; preserve proof scope and limits.
- Check complete artifact/code emission early for dependent interfaces and
  executable builders. Declaration checking alone is insufficient. Investigate
  any individual module build taking over 60 seconds before repeating downstream
  rebuilds; consult and update
  [profiling.md](docs/profiling.md) for new bottlenecks and repairs.
  Use `scripts/run-lake.sh --profile build` for automatic quiet timing and
  isolated cost diagnostics; add `--cold` for complete project-cold coverage.
  Compare quiet runs with identical thread settings; profiler frames overlap.

## Verification and working practice

- Keep tracked PDFs consistent with their current TeX sources. After changing
  a manuscript or any shared TeX input, regenerate every affected PDF and include
  it in the same commit; never commit manuscript edits with stale PDFs.
  Use `scripts/build-papers.sh` for the four main papers and the manuscript's
  established build command for other publications. Shared CCL source changes
  require rebuilding both CCL PDFs. Check that PDF generation succeeds before
  declaring manuscript work complete.
- On a working branch, build all changed Lean files before committing, with
  warnings fatal (`lake --wfail build <targets>`). No linter warnings may remain.
  The diff identifies changed filenames; do not repeat that inventory in commit
  messages. Full checks may be deferred across commits until task completion;
  track accumulated changes and affected consumer coverage.
- Use `leanOptions` name/value records in `lakefile.toml` when an option and
  its suboptions are both configured. Quoted dotted table keys are single Lean
  name components. Keep the selected native linter providers in dependency
  order so Core-only sources receive the same checks without proof imports.
  Keep every declared library/executable in `defaultTargets`; unscoped
  `scripts/run-lake.sh lint` selects all active modules and configured scripts.
  Validate options with focused positive/negative checks; `lake check-lint`
  checks runner configuration, not option validity or source compliance.
- `scripts/check-axioms.sh` is authoritative. During branch work, including
  before commits, scope audits to changed Lean modules (module names or `.lean`
  paths). Do not commit Lean changes with a known required-check failure.
  Validate generated target lists before execution; missing or empty scoped
  inventories must fail instead of selecting the default full scope.
- Changes to Lean code, including changes to scripts that produce Lean code,
  can run all completion gates through `scripts/check-all.sh`; see
  [completion checks](docs/verification.md) for coverage, caches and prerequisites.
  Such changes normally require a successful full build (`lake --wfail build`), full axiom audit
  (`scripts/check-axioms.sh --configured-scripts --full`) and full nanoda pass
  (`scripts/check-nanoda.sh`) on the final tree, including affected optional
  targets. Scoped checks do not replace these completion gates. Changes confined
  to linting or nanoda-checker tooling, including its Lean support code and
  generators, are exempt from the axiom and nanoda gates; run focused tooling
  regressions and appropriate builds. Other script-only changes require relevant
  tooling tests and build checks, but no axiom audit or nanoda pass.
  Documentation-only changes require no Lean build or proof audit.
  Include configured script owners explicitly: plain `--full` omits them.
  Compare script receipt roots by scanned module and declaration name;
  standalone modules can each declare the same basename, including `main`.
  Include selected project roots even when their worker labels them canonical;
  worker roles do not change declaration identity or project coverage.
- Serialize builds and Lean checks that import their outputs in the same
  worktree. Lake can replace artifact parts during emission; overlapping
  writers or readers can observe missing or stale parts.
  Give independent agent compilers stable artifact snapshots and separate
  outputs; final builds and audits must still use the current working tree.
  Freeze Lean source edits before an authoritative audit: its required
  support/regression build can rebuild beyond the named audit modules.
- Resume completed subagents with follow-up tasks; messages alone do not restart
  their work.
- When using subagents, output from a running build may be inspected to start
  useful work before the process exits. Without subagents, let the build process
  exit before inspecting its output. Partial output does not establish a
  successful build.
- `--no-build` requires current selected and audit-support artifacts. Audit
  receipts bind module sets, source/tool revisions and compiled private
  artifacts, including generated proof auxiliaries. A public `.olean` alone
  proves no private-body currentness. After proof dependency changes, rebuild
  the affected import closure: literal `ConstantInfo` records do not establish
  current exported-axiom cache entries. Bind complete emitted parts and retain
  those entries. Missing/stale private artifacts require rerunning the
  authoritative audit. Diagnose only reported audit failures with
  `scripts/trace-axiom.sh`; never create ad-hoc `#print axioms` probe files.
- Update AGENTS.md when new rules prove helpful. Keep it concise and actionable:
  consolidate related guidance and remove superseded rules. Put historical
  reasoning, incident details and migration narratives in the relevant linked
  documentation, not here.
- Give concrete progress updates roughly every 60 seconds: findings, remaining
  uncertainty and the next question to resolve. Explain changes of approach.
