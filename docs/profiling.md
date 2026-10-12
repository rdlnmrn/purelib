# Slow Lean code: causes and remedies

**Scope:** This file should contain ways we have found that Lean code can be
slow, how to recognize each cause, and how to resolve it. Keep reusable lessons
and useful diagnostic examples here. Execution logs, acceptance receipts,
progress reports and inventories do not belong in this guide.

The compiler-specific findings below concern Lean 4.32.2. Recheck the relevant
implementation after a toolchain upgrade. Repairs must preserve the original
mathematical contracts, executable data, cached work and constructive proof
requirements, using ordinary Lean limits.

## Identify the expensive phase

Separate imports and setup, declaration elaboration, kernel checking, module
serialization, reference emission and executable runtime. A small source proof
can generate a large dependent expression; a successful declaration check can
still be followed by expensive artifact emission. A Lake target's elapsed time
can also include many prerequisite modules.

Compare checking-only and complete artifact-emitting runs with the same source,
imports, compiler options and profiling settings. Locate expensive declarations
with complete, namespace-closed source prefixes. Native stacks help identify
active operations, but unresolved frames support only a partial diagnosis.

| Observed path or symptom | Cause to investigate | Remedy we have found useful |
| --- | --- | --- |
| `writeModule` / symbol-frequency indexing → `collectDeps` | Repeated traversal of dependent signature expressions | Shared-node dependency collection; exact proposition and parameter-type aliases |
| `mkInjectiveEqTheorem` / `mkInjectiveTheorems` → `collectDeps` | Generated injectivity proofs for dependent structures | Name data-field types and ownership/bound propositions |
| `elabFunValues` → `containsFVar` / `hasAnyFVar` | Repeated unused-section-variable analysis | Compact types; make the existing theorem telescope explicit |
| `Meta.kabstract` in a rewrite | Abstraction over a large dependent payload | Scalar congruence and explicit equality transport |
| `addSmartUnfoldingDefAux` | Large constructor expressions inside recursion | Nonrecursive constructor helpers |
| `isDefEqProjDelta`, `whnf`, `reduceMatcher?` | Conversion through computed owners or adapters | Retained fields, exact equations and targeted reduction |
| Long delay after `.olean`/IR but before `.ilean` | Reference-position processing of very long source lines | Token-preserving line wrapping |
| `environment::add_definition` | Kernel checking is active | Isolate the declaration before choosing a proof or construction repair |

`collectDeps` alone does not identify export indexing: it also runs while
constructing injectivity theorems. Relevant pinned compiler sources include
`Lean/Meta/FunInfo.lean`, `Lean/LibrarySuggestions/SymbolFrequency.lean` and
`Lean/Meta/Injective.lean`. Inspect callers as well as the hot function.

Broad builds have reported slow modules whose unchanged isolated complete
emissions were much faster. Such a replay does not establish contention as the
sole cause, but it does prevent treating an unconfirmed timing as a local code
bottleneck. Fix the source only when a reproducible cost or elaboration failure
justifies it.

When unrelated modules slow down together, check whether the host is shared
with another build before changing their proofs. Compare builds in a quiet
window with the same concurrency and dependency state; record known competing
workloads alongside the timings. A successful contended build establishes
correctness, but its elapsed time is a poor measure of a repair's speedup.

Profiler output itself can be expensive. Pretty-printing dependent trace frames
has more than doubled an otherwise unchanged replay's wall time. Nested and
asynchronous component totals can overlap; do not add them to obtain elapsed
time. Compare equivalent quiet runs when evaluating a repair. A timeout is a
lower bound, not a completed baseline for a speedup ratio.

For an automatic build report, use:

```sh
scripts/run-lake.sh --profile --cold --wfail build
```

`--cold` preserves the previous project build directory and starts with empty
project artifacts. Toolchain, dependency and operating-system caches remain;
this is a project-cold build. It also disables cache downloads. Use the same
`LEAN_NUM_THREADS` setting when comparing builds.

`--profile` first records the ordinary build, then replays freshly built modules
whose reported duration is at least five seconds. It preserves each module's
saved compiler command, setup and native providers, writing diagnostic artifacts
separately. Quiet full, import-header and checking-only runs give estimates of
setup, declaration checking and emission costs; a fourth run records profiler
hotspots. These differences are estimates from separate runs. Nested profiler
frames overlap, and tracing can itself exhaust the ordinary heartbeat budget.
Such a failed trace does not invalidate a successful quiet compilation.

Either flag can be used independently and with explicit build targets. Cached
or unselected modules are marked unmeasured. Reports and byte-checked diagnostic
checkpoints live under `.lake/build-profiles/`; repeated compatible diagnostics
reuse completed work. `CCL_PROFILE_THRESHOLD` changes the selection threshold
and `CCL_PROFILE_JOBS` selects one to four diagnostic workers. Serialize builds
and diagnostics in each worktree and keep source edits frozen throughout a run.

The pinned Lake can repeatedly replay `Task.get` backtraces from synchronous
export-info jobs while selecting projection owners' C/object facets. An
interrupted model-projection build produced tens of gigabytes of repeated
diagnostics. Stop the owned build before inspecting its log; preserve a bounded
diagnostic excerpt rather than rerunning that job. The projection control now
requires current C artifacts from a warning-fatal project build with Lake's
`--no-build` currentness check, then compiles those C files directly and emits
fresh consumer C. Its exact stored-data traversal and owner-replay checks remain
required. This avoids the redundant export-info jobs without changing proof
limits or bypassing missing/stale artifact failures.

The same issue can affect complete optional-library builds. Retrying
the complete target selection with `LEAN_NUM_THREADS=1` and `--quiet --wfail`
completed successfully. The thread setting changes scheduling; quiet mode omits
successful informational-log replay while warning-fatal checking and failure
reporting remain active. Keep the complete build selection and ordinary Lean
limits when applying this recovery.

Even on a warm artifact cache, pending import metadata can trigger the
synchronous export-info wait. Overlapping import paths can multiply inherited
diagnostics. A native dependency-join patch preserves parallel workers: the
build wrapper installs and reuses it through `scripts.toolchain.prepare_lake`.
The repair covers native Lake CLI builds; interpreted Lake API use retains the
stock kernel and IR artifacts.
The single-thread recovery above remains useful when invoking an unpatched Lake
directly. Quiet mode does not prevent the internal log growth, and the patch
does not deduplicate unrelated inherited diagnostics.

Proof-producing compiler frontends can spend the ordinary heartbeat budget on
an unsuccessful conversion before applying a retained recursive equality. In
the well-founded equation producer, attempting reflexivity on two distinct
recursive callbacks unfolded their dependent transports and polynomial
division computations. The original source compiled with the original native
frontend against the same imports, locating the regression in proof production.

Check exact expression equality first. When a distinguished recursive callback
still occurs, apply its retained pointwise equality before broad definitional
conversion; attempt direct premise application only when the goal has the
corresponding callback head. Preserve the original unsupported-case fallback.
Verify complete artifact emission of the unchanged failing source and previous
equation regressions with the actual rebuilt native frontend and ordinary limits.

For indexed results, generalizing a decision can make the target ill-typed.
Split with `byCasesDec` using the original proposition and supplied decision,
then transport the actual conditional value with explicit `dif_pos`/`dif_neg`
applications. Select conditionals from the exposed value heads; searching the
whole equality can instead select an unrelated conditional in its result type.

## Repeated imports in long-lived lint processes

Lake's builtin linter imports each selected module into a fresh environment, but
retained import allocations can accumulate within its process. With Lean 4.32.2,
individual processes grew past 60 GiB during large selections; dividing a
selection into several long-lived batches retained the same growth.

Build the complete selection once with Lake, then invoke the unchanged
`Lake.BuiltinLint.run` with exactly one module per Lean process. Process exit
releases its imported allocations. A sample of sixteen simultaneous workers
measured about 12.83 GiB in aggregate; the complete 6,896-module pass reached
about 1.87 GiB for its largest worker. Choose a pool from measured whole-process
memory, including other active audits.

The normal `scripts/run-lake.sh lint` command uses this process boundary and
checked per-module checkpoints. The launcher is compiled once with full module
initialization and interpreter support, rather than re-elaborated in every
worker. The native launcher measured 377 MiB and 1.1 seconds on
`Purelib.Data.Vector.Basic`, compared with 886 MiB and 2.7 seconds for `lean --run`
in the same environment.

On a 192-CPU host, a warning-fatal pass over all 6,900 configured modules took
4 minutes with 168 automatically selected workers and no reused lint results,
including native-launcher compilation. Input preparation took 31 seconds and
checks took 207 seconds; aggregate CPU use averaged 143 cores. An unchanged
rerun reused all 6,900 checkpoints in 20.7 seconds (16.4 seconds of preparation
and 1.3 seconds processing cached results, plus wrapper overhead). These are
host-specific measurements, not performance thresholds.

The old per-worker checkpoint validation repeatedly checked shared file
signatures: profiling a 64-module sample recorded hundreds of thousands of
file-stat calls. Batch successful completions and validate the union once before
publishing their individual atomic receipts. Keep a bounded submission queue,
report completions as they arrive and flush completed batches while slow workers
remain outstanding. Failed and unpublished results must not become passes.

`CCL_LINT_JOBS=auto` uses available CPU affinity and memory (two GiB per worker,
from the earlier full-pass peak), with an eight-worker fallback if memory cannot
be measured. An explicit positive count has no fixed tooling cap. See
[linting.md](linting.md) for commands and checkpoint recovery.
Reuse requires the exact compiled import closure, private/server/IR parts,
compiler/native libraries, helper, options and output digest. Ordinary
`--no-build lint` uses the same process boundary after Lake checks currentness
without emitting artifacts. Custom lint flags and drivers retain Lake's original
dispatch.

## Large dependent signatures and generated injectivity proofs

Theorem-suggestion indexing traverses exported theorem signatures. In upstream
Lean 4.32.2, dependency collection does not memoize shared expression nodes.
A subexpression shared in the expression DAG can therefore be visited repeatedly
through different parents. Nested projections, specialized builders and implicit
function arguments can make a short signature expensive to traverse.

The repository's Core patch visits each distinct expression once while
preserving the original sorted parameter-dependency array. This repairs the
shared-DAG traversal for export indexing and injectivity generation without
altering mathematical signatures. Recheck both returned dependencies and emitted
artifacts when updating it. Native executable replacement is essential: changing
only the source or imported `.olean` does not replace the compiler's collector.

Introduce named `def` aliases for the exact propositions and dependent
parameter or field types. Inspect the entire telescope, including ownership
equalities and bounds, as well as the conclusion. Naming only the conclusion
leaves large parameter types exposed; naming only the parameters can leave
expanded implicit function arguments in the result. Local `let` bindings do not
provide the same declaration boundary.

Dependent structure injectivity generation has the same traversal problem.
Naming data-field types alone may leave the costly ownership or bound
propositions expanded. Name those exact propositions too, keeping injectivity
theorems enabled.

This has resolved expensive emission in period-area and cut-boundary interfaces.
Aliases preserve definitional equality; they must retain the original owners,
indices, cached values and premises. Do not replace an expensive field with a
fresh preparation or weaken the claim. Give aliases the body exposure required
by their actual clients. A proof that needs the alias reduced can start with
`dsimp only [ExactPropositionAlias]` or an explicit `change`.

## Automatic section-variable analysis

Unused-section-variable analysis can independently traverse large theorem types,
proof terms and the types of other variables. The pinned `elabFunValues` path
uses `Expr.containsFVar` / `hasAnyFVar` without memoizing shared nodes.

Compact dependent parameter types and result propositions first. If analysis
still spends time scanning the proof term, declare the theorem's existing
parameter telescope explicitly instead of inferring it from the surrounding
section. Preserve the premises, binder modes, argument order and retained
ownership data, and check real downstream applications. Keep the linter enabled;
artificial `include` directives or unused parameters do not resolve the cause.

## Conversion through computed preparations and projections

Field types that project through a structure update can force conversion to
unfold the complete preparation. For example, projecting `.excision` or
`.traces` from `prepared.atDepth depth` inside a dependent structure triggered
repeated `isDefEqProjDelta` and unfolding work.

Retain the refined preparation as a field, together with its exact canonical
equality, and project dependent field types from that field variable. Consumers
that need the canonical expression can destructure the record and substitute
the equality once. This keeps the original preparation and its defining relation
without repeatedly reducing the adapter during structure elaboration.

Likewise, putting a computed `prepared.rowMagnitude ...` directly in a dependent
budget type exhausted ordinary heartbeats at `whnf`. Exact type aliases alone
did not resolve it. Retaining the magnitude as a scalar field with its defining
equality made the budget depend on the field variable and removed the costly
conversion. Builders and consumers must use that exact cache.

For a small adapter whose conversion unfolds underlying preparations, reduce
only the adapter with `dsimp only [AdapterDefinition]` before applying the cached
certificate. A type annotation alone may not expose the needed equality. Check
for redundant normalization too: a caller supplying `cache.normalize` to an
adapter that normalizes again produced `cache.normalize.normalize`, while the
certificate referred to the single normalization.

Independent kernel checking can expose an expensive conversion that Lean checks
quickly. A replay harness assigned a cached equality directly to an equality
against a traced canonical bank constructor. Nanoda unfolded the bank selection
while comparing those different heads: one declaration was still reducing after
27 minutes with roughly 86 GiB resident memory, although the executable bank
regression ran quickly.

Prove the trace's identity once over an arbitrary continuation, specialize that
law to the canonical constructor, and compose it with the retained equality
using `Eq.trans` and `Eq.symm`. This compares matching application heads without
evaluating the selection. The complete repaired harness stream checked in
1.92 seconds with about 1.38 GiB peak memory under the same pinned checker and
64-thread configuration. Keep the native marker and original computation;
verify interruption recovery, exact retained output and generator-free replay.
More checker threads cannot divide the reduction of one declaration.

## Prove scalar facts before supplying large owners

Prove the smallest generic identity at the object's existing abstraction level,
then specialize it to the retained or computed data. Reuse algebraic laws and
explicit recursion equations before expanding coordinates or asking conversion
to evaluate a large construction. Preserve the original owners, cached data and
defining equations.

For example, use matrix associativity and distributivity instead of expanding
every matrix entry into a ring goal. Rewrite a recursive operation with its
selected branch equation before transporting an equality with `congrArg`.
Local abbreviations alone do not prevent reduction: a separately proved generic
lemma keeps the expensive computation outside the proof of the identity.

A scalar arithmetic tactic can become expensive when invoked in a large
dependent context. Cut-word genus proofs and grid spanning equations became
much cheaper when their final arithmetic was moved to private lemmas over a
few natural numbers, or replaced by direct cancellation and scalar congruence.
Pass the already proved balance equation to the scalar lemma, then apply it to
the retained owners. Do not ask the tactic to preprocess the entire preparation.

Prefer a direct existing law for a simple cancellation or reflexive comparison.
For polynomial rearrangements, isolate scalar equations before using the owned
ring frontend. Split conjunctions before scalar Omega calls and clear irrelevant
existential assumptions. These steps also help preserve the intended proof
closure.

The same boundary helps builders. Prove a rescaled error bound in a helper
parameterized by the retained boundary and exterior preparation, then construct
the geometry and apply that helper. Proving the bound inside a constructor that
also expands both preparations caused expensive kernel work. Root-owner request
construction was similarly repaired by separating the scalar comparison from
the cached frame construction.

A large finite case proof can be factored into small scalar row lemmas. This
resolved a sixteen-case Dirichlet proof without changing its diagonal witnesses,
formulas or case-selection procedure.

Ring normalization also unfolds local coordinate abbreviations. Put the final
identity in a private lemma over independent norm, dot-product and determinant
scalars, then supply the small coordinate identities. Symmetric polynomial
variables such as side sums and products reduce the degree before normalization.
These changes preserve the original geometric claim while avoiding a much larger
coordinate expansion. Apply an existing recurrence formula before expanding a
high-degree polynomial composition.

For closed box refinements, prove the four scalar endpoint inequalities directly.
Using reflexivity can force conversion of two independently computed large owner
records even when their displayed boxes agree. For dependent finite recursion,
use the branch equations needed by the proof instead of synthesizing the general
`eq_def` rewrite theorem for the entire match.

## Large rewrites and dependent readback comparisons

Rewriting inside a large dependent payload can spend time in `Meta.kabstract`
or conversion. Use `Eq.mpr`, `congrArg` and `congrArg₂` to transport small scalar
equalities over the actual retained data. Avoid asking a rewrite to abstract
over an entire geometry, owner or cached conditional.

Stationary matching proofs provided a useful reflexivity case: `rfl` over the
complete dependent frames was expensive. Explicitly changing the goal to the
equality of their retained projection-order `forward` operations before `rfl`
gave the kernel the smaller scalar expression. The frames, overlap witnesses
and inverse certificates remained intact.

For shared-side adapters, an explicitly typed local `let` for cached
`OwnedReadings`, followed by an explicitly typed pointwise readback, let the
generic constructor elaborate promptly. A `have` binding hid the readings'
defining equality and failed the readback check. Transport area through the
small path/group equalities with scalar congruence rather than rewriting through
the whole dependent wrapper.

Comparisons of cached records with functional fields can be much more expensive
than comparisons of their operations. Exact owner-type aliases, generic
heterogeneous transport lemmas and branchwise conditional-operation lemmas
allowed endpoint protocol comparisons to complete. Such a comparison establishes
only its stated relation; it does not imply equality of an unexamined functional
record. Choose the comparison that the actual preservation contract requires.

## Inference across different scalar presentations

Unification can repeatedly unfold large objects when bounds mix canonical
Gaussian quadrance with a squared-norm adapter. Specialize each retained scalar
certificate first, transport it with the existing `normSq_eq_canonical` equality,
and only then combine the bounds. Keep one scalar presentation within a local
proof; cross the exact bridge at its boundary.

This resolved heartbeat failures in handle-area, square-root and primitive-path
bounds. Explicit point arguments and retained index bounds can also prevent
inference from reconstructing an owner-dependent record. Reduce the necessary
scalar definitions rather than simplifying an entire function or shared list
tail.

## Tactic frontends repeatedly visiting expressions

Proof reconstruction can repeatedly traverse shared expression nodes. The
quotient-free Omega frontend spent most of its time interpreting certificates
when its recursive traversal revisited the same nodes and application spines.

The successful repair uses a fresh `MonadCacheT ExprStructEq Expr MetaM` per
proof, traverses original binary children with `Expr.traverseChildren`, and then
performs the unchanged root reconstruction. Structural keys retain binder names
and annotations; bound variables are not opened or reabstracted. Generic
`Core.transform` flattens application spines, while `Meta.transform` also opens
binders, so neither traversal policy preserved the required reconstruction.

Constant replacement in the ring frontend had a related avoidable cost:
sequential name checks at every node. A finite hash map of the same replacement
functions, an immediate skip for nonconstant nodes and one lookup per constant
removed those repeated checks. Keep the normalizer, universes, original argument
expressions and certificate packaging unchanged. Kernel-check quantified
regressions and audit generated auxiliaries after a reconstruction change.

## Large dependent constructors inside recursion

Structural recursion over data can generate costly smart-unfolding equations
when recursive branches contain large constructor/projection expressions.
Factor singleton, append or other dependent result construction into small
nonrecursive helpers, called from the original recursive equations. This
resolved both checking and emission cost in coordinate factorization while
retaining the degree decrease, finite factors and evaluation identities.

Check executable emission early: a direct induction or recursor term can pass
declaration checking yet fail code generation. Keep the recursive algorithm,
termination evidence and cached tails intact. Recursive callbacks also need
controlled unfolding: use an explicit one-step equation when available rather
than registering a simplification rule that repeatedly expands the fixpoint.

A dependent multiargument dispatcher exposed a separate equation-generation
failure at `Lean.Elab.WF.mkBinaryUnfoldEq`. Packing the varying arguments into
the same dependent tuple used by the recursion compiler avoided the additional
public-wrapper equation step, retaining the original finite measure and branch
order. Use this workaround only for that diagnosed wrapper failure, and verify
actual unfolding behavior in its clients.

## Closed numeral proofs and executable casts

Large rational numeral casts can reduce through a recursive natural or integer
cast. Closed `decide` proofs over those casts have overflowed an independent
checker's stack; inference of cast indices has also reached Lean's ordinary
recursion limit.

For positivity or ordering of natural casts, apply the owned `natCast_pos_direct`
and `natCast_le_direct` lemmas to natural inequalities, supplying indices
explicitly when needed. Reuse positivity for nonnegative and nonzero obligations.
For exact interval-arithmetic regressions, rewrite with `natCast_eq_fromInt`
first, then kernel-check the direct denominator-one records. Inspect the complete
proposition and named fixture definitions: small literals inside powers or
loops can still produce large computations. A specialized scalar certificate
can use `simp only [Nat.cast_ofNat]` to align numeral presentations without
evaluating the unary cast.

Executable casts need attention as well. A generic integer cast used by a
Gaussian-integer embedding failed to finish on a large denominator. Selecting
the existing denominator-one `Fraction.Cast.fromInt` operation for both
coordinates removed that unary-cast computation; complete record equality for
all signed inputs preserved the mathematical result and existing instances.
Force actual digit or coordinate observations in runtime controls: an unevaluated
`let` marker does not measure the computation.

The same failure occurred when an RFAP continuation regression evaluated a
Pell ratio and its robustness payments. Natural Pell coefficients, denominator
quadrances and ceiling weights reached `Nat.unaryCast` and exhausted the
interpreter stack while realizing the initial reserve, before any additional
request could finish. Convert these
executable quantities with `Fraction.Cast.fromInt` on their original natural
values, and retain the old cast formulas through `natCast_eq_fromInt`. Consume
those exact formulas in existing proofs instead of unfolding the replacement
computation. Keep the interpreter stack and ordinary Lean limits unchanged.

The compiled continuation regression exposed the same large natural cast in
the general cylinder coefficient cutoff. Its overflow handler blocked while
reading the thread's stack attributes: elapsed time kept increasing while
CPU time stayed nearly constant. Inspecting the owned process's native
frames identified the repeated `Nat.unaryCast` calls behind that apparent
wait. Repair the mathematical owner's actual cast and retain its original
formula; changing the regression backend alone does not remove the cost.

## Large finite tables and selectors

Putting many dependent certificate constructions in one decision tree can
exhaust elaboration limits even when every scalar check is cheap. Factor the
original certificates into named rows or named construction bodies and let the
selector return those retained values. A result-type abbreviation alone may
leave the construction expanded.

Generated finite matrices also became cheaper when their computed concrete
width was stated at the data boundary, instead of repeatedly converting a
length such as `word.alphabet.count`. Keep the downstream dependent spanning
certificate and its exact row equations.

Selector shape affects client reduction. A primitive `Nat.casesOn` renderer
left projected finite numerals beneath `Nat.rec`, preventing a scalar Gaussian
simplification. Nested structural zero/successor matches restored that reduction.
Check arbitrary-input agreement of complete selected records and existing
clients' actual unfolding; equal outputs alone do not preserve simplification.
For endpoint bounds, select the retained unequal certificate directly rather
than trying expensive reflexivity first.

Finite certificate search should select its known schema directly. Trying every
positive polynomial template in each Gaussian coefficient case repeats failed
ring normalization. `scripts/generators/critical_exterior_proofs.py` selects the
original first successful template with integer coefficient arithmetic; the
emitted Lean proof still checks every identity. Run it without arguments, and
with `--two-parameter`, to check reproducibility; use `--output PATH` to regenerate.

For small finite sign tables, split the structural cases and sign values, then
revert independent Boolean inputs and use kernel `decide` for their quantified
truth table. Splitting every Boolean into another tactic branch duplicates the
same elaboration work. Keep the original all-input theorem and proof closure.

## Generated proof size and reference emission

Materializing large constructor proof terms can multiply source size and
conversion work. Prefer compact theorem-schema applications or readable
constructor proofs. Share repeated application nodes only within the matching
local context, and limit lexical nesting to keep ordinary recursion limits.
Some expanded dependent constructor proofs still failed after aliases and
annotations; smaller source alone did not establish a successful repair.

Very long rendered lines introduce a separate cost after module serialization.
Pinned Lean's frontend converts reference positions to UTF-16 columns by
traversing each line prefix. Repeating that work across a huge proof line made
`.ilean` emission dominate despite quick declaration checking.

Deterministic wrapping at about 120 columns removed that bottleneck in a
constructor-certificate experiment. Preserve quoted identifiers and all
non-whitespace tokens, and compare complete compiled records when changing
rendering. The experiment was later discarded; the reference-emission lesson
remains useful without implying that its expanded proofs are installed.

## Module boundaries and dependency fanout

A module with several independent expensive proofs can lengthen the build path
for every consumer. Separate shared construction from independent bound families
and keep late adapters after those families. This allowed parallel compilation
of independent dyadic refinements. Moving an early preparation API ahead of a
costly dependent walk also let early consumers finish without waiting for the
walk; it did not make the late proof intrinsically cheap.

Split at actual objects and dependency boundaries. Sequential generated
certificate chains can be split at complete declaration boundaries, while
independent families can compile as siblings. Avoid arbitrary one-definition
modules. Change the owning generator, preserve exact witnesses and certificates,
and verify reproduction instead of editing generated outputs independently.

Use narrow direct imports. Aggregate facades and example umbrellas can pull
thousands of prerequisite jobs into a small provider build. Separate per-module
compiler cost from the cost of refreshing its consumer closure; preserve
completed Lake artifacts and schedule shared prerequisites before large
aggregate targets. The final affected-consumer check is still required.

Give reusable modules one Lake library owner. Overlapping reusable roots in
checkpoint libraries have produced native library emission cycles even with an
acyclic source-import graph. Checkpoint libraries should declare their script
roots and obtain reusable modules by import. Reusable library facades must also
avoid pulling optional example libraries back into their own dependency chain.

## Missing names can look like slow proofs

Unresolved owner names can become auto-implicit variables in dependent
signatures, causing costly unification and cascading heartbeat failures. Missing
public import paths and wrong helper argument order have produced the same
symptom. Inspect the earliest unknown identifier or type mismatch before
profiling later proof failures.

Open the actual declaration owner, restore required public dependency paths and
supply the exact declared parameter types and argument order. This has resolved
long failed elaborations in prepared bridges, reciprocal-disk boundaries and
crossing certificates without changing any Lean resource limits.

## Runtime cost of constructive replacements

Mathematically equal executable operations can have very different costs. An
owned finite low-bit recurrence for unsigned xor measured hundreds of times
slower than Core's primitive operation on the same workload. Equality of its
unsigned results did not preserve diagnostic throughput.

Measure the actual forced runtime observations after changing an executable
route. Account separately for preprocessing, such as denominator norms and
logarithmic widths, and for the arithmetic loop itself. Reuse retained summaries
and caches where the contract permits; do not substitute an unchecked native
implementation to recover speed. A faster preparation does not establish that
every downstream computation is faster.

## Repeated verification of shared proof closures

Independent exports and checker processes can repeatedly load and check the
same large proof closure. Topological ordering alone does not remove that work.
Group roots that share expensive dependencies when measured complete closures
fit the measured memory budget, and reuse completed exports and successful checks
only under exact input and content identities.

Root counts and summed per-declaration expression estimates are weak proxies
for cost: interning across declarations varies considerably. Every independent
stream still needs its complete dependency closure. A limit checked after a
root finishes is not a strict memory ceiling, and an uncalibrated overlap model
does not establish a production speedup. Merely keeping a checker process alive
also does not establish safe cross-stream reuse of expression identities.

Repeated decoded import environments can dominate memory in host audits.
Whole-worker measurements showed heavily overlapping imports consuming roughly
8–10 GiB per process; full-repository host exporters later exceeded 70 GiB
each. Measure workers through chunk production, rather than only at startup.
Size concurrency from measured whole-worker RSS and the
combined workload budget, rather than CPU count or the number of assigned roots.
More parallelism can add memory pressure and duplicate import/setup work.

The completion runner distributes discovered tooling tests into separate
processes rather than running the entire fixture suite serially. Before this
change, the tooling stage took 1,115 seconds of a 1,851-second full run. Small
fixtures reserve two GiB and heavy host-reader fixtures reserve twelve GiB;
unknown new fixture modules receive the heavy reservation until reviewed.
Tests compile into their own temporary outputs against stable project artifacts.
The full-inventory native nanoda benchmark reached 32.70 GiB combined RSS with
three exporters and three two-thread checkers; its largest sampled process was
12.39 GiB. Completion scheduling reserves sixteen GiB per process and budgets
both pools together. `scripts/check-all.sh --max-cores N` limits inherited CPU
affinity and sizes these pools, while per-test reports retain actual concurrency
and sampled RSS for later calibration.

Measure cold export/check caches and warm replay separately with
`python3 -m scripts.nanoda.benchmark_pipeline --output .lake/nanoda-benchmark/RUN`.
Use `--manifest` for a focused scope and explicit worker counts for comparisons.
Each output directory must be new; the command retains its isolated cache,
logs, stream hashes and input/checker receipts. `NANODA_CACHE_ROOT` also isolates
all production cache families when running `scripts/check-nanoda.sh`
directly. Pipeline wall time includes artifact freshness checks, hashing and
queueing; exporter phase timings and sampled process RSS are separate. Summed
RSS can count shared mappings more than once. Declaration-name multiplicity
across streams measures repetition, not interchangeability of same-named
standalone script declarations.

The native producer preserves one shared expression graph across ordinary
modules and memoizes metadata removal across declarations. This avoids rebuilding
comparison-oriented host representations and exporting foundations repeatedly.
Independent root selection and output coverage validation still have costs:
measure them separately from native import and serialization. Keep conflicting
standalone environments separate even when their declarations have equal names.

Unfolding all geometric coordinates before one `ring1` can leave a large
normalization proof whose individual nanoda check dominates the shared graph.
Use declaration timings to identify that cost. A repair should factor the
identity into smaller checked algebraic steps while preserving its claim; it
requires separate proof validation from an export or scheduling change.

Use the pinned checker's normal parallel path for the larger graph. With one
thread it checks on the main thread, whose stack is smaller than its own worker
stacks. A serial stack overflow does not establish that export or parsing is slow.
Use the same thread configuration in comparisons; do not raise Lean limits or
replace proofs to hide a scheduling/configuration mismatch.

For separate parser and kernel timings, build the pinned library diagnostic
driver with `scripts/build-nanoda-profiler.sh`, then run its returned binary with
`CONFIG --parallel < STREAM`. It calls the stock CLI's `check_all_declars` entry
point using the configured thread count and reports `parse_ms` and `check_ms`
separately. Use `CONFIG --individual < STREAM` for individual declaration timings
on the same parallel configuration and normal pinned worker stacks. It records
active declarations and reports completed checks taking at least 100 ms.
Omit the flag with a serial configuration for small-stream diagnosis.
These diagnostic reports are not production checker receipts;
retain the ordinary empty-axiom check through `scripts/check-nanoda.sh`.

## Diagnose the build driver before blaming a proof

A build of Boolean vectors, rational literals and Gaussian norm bounds hit a Lake export-info task panic before any source edits. The
owned Lake process had no compiler descendants while repeated
`Task.get`/`sync := true` backtraces grew its memory to about 73 GiB and its
redirected log to 180,687,396,282 bytes. This was build-driver diagnostic
work, not a slow Lean declaration. Stop only the verified owned supervisor
and descendants, preserve emitted artifacts, and keep a small diagnostic sample
instead of the repetitive log.

Isolating the small providers and then the bounds provider with explicit
`:leanArts` targets completed successfully using the existing caches and
ordinary Lean limits. This facet emits the public/private/server kernel parts
and IR; it does not replace final full build or proof checks. Treat that result
as a measured recovery for this invocation, not a compiler fix. Check the
owned process tree and whole-worker memory before retrying a slow batch;
without subagents, inspect its log only after the build has exited.

For a driver that supports bounded recovery, retain a small panic diagnostic
and retry the identical target selection with one Lake thread. A failed serial
retry can be split into smaller groups; an ordinary compiler or linter failure
must stop the run. This changes scheduling, not the toolchain or proof limits.

Reuse successful module work through atomic checkpoints bound to current source
and complete emitted artifacts. Missing or changed parts invalidate the
checkpoint. Keep captured inputs immutable for independent offline reviews;
current-tree builds and authoritative audits remain serialized.

During the revised rotation-publication work, a 32-thread scoped build of
`Purelib.LinearAlgebra.Coordinates3.Ray` hit the same `Task.get` panic in
Lake's export-information tasks. The process exited with a normal source
error, leaving a 23,735-byte log and no live Lean or Lake workers. After
repairing that source error, direct file compilation through `run-lake.sh env
lean`, using the emitted setup JSON and `LEAN_NUM_THREADS=32`, succeeded with
all kernel, server and code outputs requested. This preserved the requested
32-thread setting and cached work. It establishes focused artifact emission;
the final full build and proof checks remain separate acceptance gates.

## Keep profiling setup cheaper than the probe

Preparing a full symlink overlay of the same immutable artifact tree for every
worker multiplied filesystem work before Lean started. Separate input
preparation from compilation and reuse content-bound Lake `importArts` mappings
or checked prepared input trees. Preserve module, package, options, private
imports, server/IR parts and execution artifacts; keep outputs separate from
immutable inputs. Measure setup and compiler time independently.

Full `repr Expr` output can likewise expand shared subexpressions into gigabytes
of text. Use bounded structural fingerprints and constant/shape reports for
triage, and print full expressions only for small selected declarations.
Fingerprints do not replace exact equality checks. Cache immutable dependency
facts within a transaction instead of repeatedly rediscovering or parsing them;
working-tree and artifact currentness must still be checked.

Store shared input manifests once and reference checked receipts from per-module
summaries. Checkpoint completed rows individually or in small batches instead
of repeatedly rewriting an expanding aggregate; write the compact final report
once. Duplicating complete import manifests can make report serialization cost
more than compilation. For a frozen input tree, cache fingerprints within the
run and revalidate the complete input set at the end. Keep mutable outputs under
the ordinary per-read checks and reject the run if an input changes.

## Reuse completed work, not just logs

Expensive generators, executable harnesses and profiling drivers need atomic
incremental checkpoints and checked reloads. Save completed stages with their
exact source, toolchain, options, dependencies and output identities. A changed
input invalidates the affected stage and its consumers; unrelated completed
work should survive. Separate input discovery/hashing from compiler time when
reporting iteration cost.

Logs and final snapshots alone do not provide restart. Exercise interrupted-run
recovery with a completed producer that fails if called again, and verify that
missing or corrupt artifacts are rejected. Preserve compatible artifacts across
harness changes through explicit checked adoption. Keep numerical consistency,
executable provenance and reconstructed ownership certificates distinct.
See [certified restarting](certified-restarting.md) for the full contract.

Before replacing a running driver, identify and stop its supervisor and owned
descendants, preserve checkpoints and confirm that no superseded worker remains.
Detached workers have continued spending CPU after their old supervisor's
implementation was replaced.

Serialize Lake writers and checks that read their outputs in the same worktree.
Concurrent consumer builds after a provider edit have raced while emitting the
same stale prerequisites, producing missing or empty artifact errors and
repeating compilation. Refresh shared prerequisites once; use immutable input
snapshots and separate outputs for genuinely independent compilers.

## Apply and verify a performance repair

Use the [profiling driver](../scripts/profiling/branch_builds.py) with current
prerequisites and an existing repository module:

```sh
python3 -m scripts.profiling.branch_builds --stage module \
  --module MODULE --check-only --quiet
python3 -m scripts.profiling.branch_builds --stage module \
  --module MODULE --emit-code --quiet
```

Omit `--quiet` to collect Lean profiling output. Use a complete, namespace-closed
candidate with `--source-file /tmp/candidate.lean` to isolate declarations without
changing production sources. Native stack probes are diagnostic samples, not
successful build results. Use the driver's checked provenance reload for
compatible inputs and keep source, imports and artifacts fixed during a probe.

Change one identified cause, compare equivalent complete emission runs, and
revert speculative changes that do not materially help. Check all required
artifacts: in the pinned compiler, `--run` can execute a script while omitting a
requested C output, so executable success alone is not full emission.

Confirm local gains in a complete project-cold build with the same thread count
and comparable dependency state. Report build wall time separately from the
subsequent diagnostic replays. If the complete build slows down while isolated
compilation stays fast, investigate scheduling, competing work and dependency
rebuilds before attributing the extra time to the source proof.

Validate real consumers, defining equations, executable behavior and the proof
closure under [AGENTS.md](../AGENTS.md). After a proof-provider change, rebuild
the affected import closure before auditing: literal declaration records do not
establish current persisted exported-axiom entries. Bind complete private and
public artifact parts. Follow the authoritative build, axiom and nanoda gates;
a local timing improvement does not establish task acceptance.
