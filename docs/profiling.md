# Diagnosing and fixing slow Lean builds

Use this guide to locate expensive module builds and repair their causes.
It covers elaboration, kernel checking, generated declarations, artifact
emission, imports and build scheduling. Keep execution histories and numerical
benchmark tables out of this document.

Use ordinary Lean limits and preserve mathematical contracts, retained owners,
executable data and constructive proof dependencies. Compiler internals below
refer to the pinned toolchain; recheck them after a toolchain upgrade.

Before integration into `master`, changed project modules and consumers affected
by the changes must build in under 30 seconds with current dependencies and
complete artifact/code emission. An unchanged consumer can become slower through
changed imports, exposure, inlining or instance selection. Unaffected modules
need no profiling or repair for this task. Branch work and checkpoint commits
may retain documented timing debt. Measure actual recompilation; a cached Lake
check establishes no per-module timing. This performance target excludes
third-party code, including the pinned Lean toolchain; the two-minute build watchdog
still applies. See [timing scope](verification.md#timing-scope-and-measurement).

Run nanoda and the full integration suite when ready to merge into `master`;
use incremental builds, axiom audits and lint during ordinary branch work.

Each individual module build must start under a two-minute wall-clock watchdog;
regression tests retain their five-minute watchdog. Both have a fifteen-second
termination grace. Send SIGTERM at the applicable limit and SIGKILL after the
grace if needed; the emergency limit does not replace the 30-second target.
Investigate an overrun immediately before retrying or continuing dependent work.
Use the repository's guarded build and test runners; standalone regressions need
equivalent process supervision. Full builds, test suites, lint, axiom audits and full nanoda runs may take longer than five
minutes in aggregate. Keep their progress and process supervision active.
Numerical computations, harnesses and generator jobs retain the five-minute
limit on every branch. Avoid blind retries after an overrun; bounded diagnostics,
controlled timing comparisons and required verification may rerun unchanged code. Preserve
completed artifacts, verify that the supervisor and descendants have exited,
and retain the original mathematical requests and budgets.

For an explicitly user-authorized release budget, guarded Lake compilation can
use `CCL_MODULE_TIMEOUT_SECONDS` up to 300 seconds. Diagnose overruns first;
do not raise this automatically or change Lean's mathematical resource limits.
The normal deadline remains two minutes. Module receipts, guard metadata and
completed-check input bindings retain the actual selected budget.

Keep the compiler SDK path stable when only its host supervision changes.
Renaming the SDK changes compiler/C command paths and can invalidate valid build
traces even when the compiler and headers are unchanged. The guard reuses a
validated existing overlay for the same SDK and entry point, atomically updating
its complete helper/deadline binding. A changed compiler gets a different overlay;
damaged entry points, SDK links or the copied Lake binary prevent reuse.

## Identify the expensive phase

Start with a focused profiled build, replacing `MODULE` with the existing
module name:

```sh
CCL_PROFILE_THRESHOLD=30 scripts/run-lake.sh --profile --wfail build MODULE
```

The wrapper records the ordinary build, then diagnoses freshly built modules
whose reported duration reaches the threshold. Reports live under
`.lake/build-profiles/`. Cached modules are unmeasured. Lower
`CCL_PROFILE_THRESHOLD` only for a focused investigation;
`CCL_PROFILE_JOBS` selects one to four diagnostic workers.

Separate import/setup time, declaration elaboration, kernel checking,
serialization, reference emission and native code generation. The diagnostic
replays compare quiet full, import-header and checking-only runs, then collect
Lean profiler output. Their differences estimate phase costs from separate
runs. Nested profiler frames overlap, so their totals cannot be added to obtain
elapsed time. Trace formatting can itself dominate a run or exhaust heartbeats;
compare quiet runs when judging a repair.

For compiled dependency traces, large expression types can share subterms whose
expanded representation is much larger than their retained graph. Keep diagnostic
previews bounded while formatting, before constructing the complete string.
`scripts/trace-axiom.sh` bounds expression previews and still traverses complete
dependency closures; an elided preview does not shorten the proof audit.

Broad parallel build timings include contention between compiler workers.
Replay a threshold-crossing module in isolation with the same thread setting
and stable imports before changing its proofs. If the delay disappears, reduce
simultaneous compilers and use smaller target batches; retain the completed
artifacts rather than restarting the full selection. Report timing variability
under comparable conditions; selecting only the fastest run does not establish
master readiness when comparable runs repeatedly exceed the target.

An edited owner can invalidate a long chain even when every individual job
finishes under 30 seconds. Measure those jobs separately from aggregate duration.
Verify shutdown after an interrupted build, retain completed artifacts and
record jobs reaching 30 seconds for master integration. Diagnose immediately
when an overrun blocks the requested work or reaches the runaway limit.
If quiet checking alone reproduces the full cost while the import
header is cheap, focus on declaration types, conversion and proofs; an emission
or native-code repair is not yet justified.

| Symptom or sampled stack | Investigate | First repair to try |
| --- | --- | --- |
| A small target launches many prerequisite jobs | Import fanout and stale dependencies | Narrow imports and build the actual provider before aggregate targets |
| `writeModule` / symbol-frequency indexing → `collectDeps` | Traversal of large dependent signatures | Exact named parameter-type and proposition aliases; check the installed compiler collector |
| `mkInjectiveEqTheorem` / `mkInjectiveTheorems` → `collectDeps` | Generated equality helpers | Name dependent field types and ownership/bound propositions |
| `elabFunValues` → `containsFVar` / `hasAnyFVar` | Section-variable analysis | Compact types and write the existing parameter telescope explicitly |
| `Meta.kabstract` during a rewrite | Abstraction over a large dependent payload | Scalar congruence and explicit equality transport |
| A bound proof reconstructs dependent owners before applying an existing theorem | Repeated elaboration and conversion of the retained construction | Apply the existing certificate and transport its scalar readbacks instead |
| `isDefEqProjDelta`, `whnf`, `reduceMatcher?` | Conversion through computed owners or adapters | Retained fields, readback equations and targeted reduction |
| `addSmartUnfoldingDefAux` | Large constructors inside recursive equations | Nonrecursive constructor helpers |
| `environment::add_definition` | Kernel checking of the current declaration | Isolate that declaration and reduce its conversion or proof-term cost |
| `foldRelevantConstants` / `getFunInfoAux` beneath `LibrarySuggestions` | Theorem indexing over large dependent interfaces | Compact exact statements; separate coherent construction and readback groups along their dependency chain |
| `toLCNFType`, `isPropFormer`, or `inferLambdaType` beneath the compiler | Repeated conversion of dependent runtime types | Reuse complete type-conversion results within one visibility context; preserve binder metadata |
| Long delay after kernel/IR output but before `.ilean` | Reference-position processing | Wrap long generated source lines without changing tokens |
| Repeated Lake `Task.get` backtraces without compiler children | Build-driver scheduling | Inspect the owned process tree and use the build-driver recovery below |

An aggregate build exceeding two minutes can consist of many short modules
along one sequential import path. Read the completed job timings and pending
target closure before choosing a module to replay. Reuse completed artifacts and
profile the largest actual contributor with stable dependencies. Fix its measured
cause; increasing concurrency cannot shorten that dependency path.

For repeated small fixture commands, capture the checked Lake environment
once while project artifacts remain stable. Resolve the guarded Lean and
other executables from its `PATH`, and reuse that environment with each
fixture's original source paths, setup, options and plugins. Repeated
toolchain selection can dominate the actual fixture work. Capture a new
environment after changing the project artifacts or toolchain.

Inspect callers as well as the hottest function. `collectDeps`, for example,
runs during both export indexing and injectivity generation. Relevant compiler
sources include `Lean/LibrarySuggestions/SymbolFrequency.lean`,
`Lean/Meta/Injective.lean` and `Lean/Meta/FunInfo.lean`.

Check CPU use and the owned process tree before interpreting a silent build as
a stalled proof. A waiting main thread may have an active compiler worker.
Native stack samples locate active operations; unresolved symbols support only
a partial diagnosis.

A long `Kernel` profiler frame can include waiting for earlier compiler tasks.
If that worker is blocked in `to_kernel_env` or `Task.get`, inspect the active
workers before changing the declaration's proofs. Time the actual kernel
operations separately when the broad frame and native samples disagree.

When rendering trace expressions dominates the diagnostic, use
`trace.profiler.output` with `trace.profiler.output.pp=false`. The structured
export retains subsystem timings and tags without formatting full expressions;
pretty-printer depth limits do not bound every raw trace message.

If the profile contains many generated `_proof_` helpers whose bodies merely
apply existing theorems, inspect nested-proof abstraction. Rechecking each
specialized dependent telescope can dominate a small source file. The checked
frontend selected by `scripts/run-lake.sh` retains accessible theorem applications
with their original arguments when the application does not use dependent local
`let` values. Keep ordinary abstraction for lambdas, inaccessible heads and
applications using those values: the subsequent `letToHave` pass relies on
those proof boundaries. Kernel checking still checks the resulting declarations.
Its type-conversion cache uses complete expression metadata and separate caches
for private and public visibility checks. Keep rejection controls for both
kernel errors and public compilation-type mismatches when changing this path.

Repeated `MetavarContext.MkBinding` work beneath `elabLetDeclAux` can come from
nested term-style `have` declarations retaining unresolved dependencies through
the remaining construction. Elaborate the pure branch in a `by` block with
local proof statements, preserving its original computations and cached values.
Compare complete emission and generated executable code; adding a result-type
annotation alone may leave the expensive abstraction unchanged.

An `Encoder.Integral.encodeTail` stack in a prefix regression can indicate
unrequested terminal encoding. `Recording.Family.build` constructs complete
continuations, including terminal words, even when a client reads only each
leaf's admission. For finite prefix checks, build the separated box tree once
and use `Recording.admitWith` on its retained samples through
`Enclosure.realizeSample`. This keeps the actual recording, parser constraints
and window bounds. Exercise automatic terminal completion on small dedicated
continuation cases and retain the general kernel-checked continuation laws.

A rational GCD sample under path-cofactor reconstruction can come from adding
or subtracting large affine images. Check whether the Gaussian cofactors can
be combined before substitution, so cancellation occurs before multiplication
by the path coordinates. Normalize the resulting coordinate projections and
prove equality of complete coefficient tables, including leading-zero cases.
Retain the original checked column, safe predicate and complete coprimality
certificate; a matching evaluation at selected points alone is insufficient.

For linear cofactors, inspect whether substitution constructs a whole Gaussian
product before discarding one coordinate. The
[normalized path readers](../Purelib/Polynomial/Dense/Gaussian/Path/Components.lean)
compute only the requested scalar coordinate for that table shape and retain
the original Horner fold for every other shape. Their laws identify complete
normalized coefficient tables, including zero leading coordinates. Measure
saved columns in both directions before adopting a different arithmetic route:
common-denominator clearing can cost more than the intermediate reductions
it removes on short tables.
## Isolate the expensive declaration

Use the [module profiling driver](../scripts/profiling/branch_builds.py) to
compare checking with complete artifact emission against current dependencies:

```sh
python3 -m scripts.profiling.branch_builds --stage module \
  --module MODULE --check-only --quiet
python3 -m scripts.profiling.branch_builds --stage module \
  --module MODULE --emit-code --quiet
```

Omit `--quiet` for Lean profiler output. Add
`--source-file /tmp/candidate.lean` to test an isolated candidate or a complete,
namespace-closed source prefix without editing production sources. Preserve
imports, options, local instances and section context. Compare prefixes at
complete declaration boundaries to locate the first expensive declaration.

The driver runs bounded diagnostic probes. An interrupted probe gives a lower
bound on cost, not a successful baseline. `--native-stack` samples only the
isolated probe; a stack sample does not establish complete emission. Keep the
original source, imports and artifacts fixed during each comparison.

Inspect the earliest source error before profiling later failures. Missing
owner names can become auto-implicit variables in dependent signatures;
missing public import paths or wrong helper argument order can cause long
unification attempts. Restore the actual owner, parameter types and required
imports before changing the proof.

For heartbeat failures, retain phase markers at proof entry and before the
suspect operation. Measure `IO.getNumHeartbeats` relative to the current
`Core.Context.initHeartbeats`, and record the current maximum alongside it.
The final reported argument may only exhaust a budget spent on earlier
statement or proof elaboration. Compare the same retained source and setup
with the batch and native editor frontends when their results differ.

## Compact dependent signatures and generated helpers

A short declaration can contain a large shared expression graph. Dependency
indexing or generated equality proofs may traverse that graph repeatedly.
Inspect the entire telescope, including implicit arguments, ownership equations
and bounds, rather than only the conclusion.

Introduce named `def` aliases for exact parameter types, dependent field types
and propositions. Naming only the result leaves expensive parameter types
expanded; naming only data fields leaves ownership and bound propositions
exposed. Local `let` bindings do not provide the same declaration boundary.
Preserve original owners, indices, witnesses and binder modes, and expose alias
bodies only where clients need reduction.
Name proof-rich dependent-product element families before passing them through
inferred lookup arguments, so lookup elaboration retains that type boundary.

If sampled stacks identify `letToHaveValue` and `Meta.letToHave`, inspect the
optional declaration cleanup pass separately from proof elaboration. For a
dependent owner transport whose retained lets must stay intact, scope
`set_option cleanup.letToHave false in` to that declaration. This preserves the
original construction without increasing resource limits. Check complete code
emission and the resulting kernel proof closure afterward.

If `ToDepElimPattern.savePatternInfo` dominates a deeply nested tuple pattern,
read the required fields through projections and bind shared retained tails.
This avoids constructing a large dependent matcher for a readback. Preserve
the original field identities and check existing reduction laws and consumers.

If stacks show the unused-section-variable linter repeatedly calling
`containsFVar`, check its variable identities before changing the telescope.
An `include` cannot avoid that scan when the checker compares hygienic IDs
with source names. Before applying a local exception to this check, compare
the compiled parameters and binder modes and verify each parameter's use in
the retained type, body or dependent binder types. Traverse the shared
expression graph with memoization; keep other lint and proof checks enabled.

If theorem-symbol export is expensive, place the entire quantified telescope
inside a closed proposition alias. A parameterized alias can leave the same
large dependent arguments visible to the collector. Preserve binder names,
modes, ownership equations and the original opaque proof implementation.
Keep named witnesses used only by the proof: callers may supply them by name.
If the alias's conclusion omits such a required premise, scope any unused-variable
linter exception to that alias and explain the retained witness.

For equalities between staged procedures, compare each phase with an arbitrary
opaque unavailable suffix, then compose complete result equalities with
`congrArg`. Expanding all suffix closures in one proof can duplicate the later
branches and exhaust ordinary heartbeats during reduction. Use proof-phase
markers and `Lean.getRemainingHeartbeats`, measured against the current
`Core.Context.initHeartbeats`, to distinguish that cost from statement
elaboration. Keep the original request bits, branch order and complete result
in the resulting regression.

A concrete transport result can still force conversion through computed
geometry when its type spells out the mapped path and endpoint owners.
Name that exact result family beside the generic transport, where its cache
and path parameters are abstract, and instantiate it in the concrete client.
An alias declared only in the concrete client still has to elaborate the
computed expression. Keep geometry opaque and consume its original pointwise
factory equality when applying the transport.

Distinguish this elaboration boundary from compiler type normalization. If
`Elab.definition.value` and the final body marker finish cheaply but
`Lean.compileDecls` exhausts heartbeats in `whnf`, inspect LCNF type conversion.
It unfolds aliases with full transparency, so local irreducibility cannot
hide a dependent pair's fields. Repeated higher-order use can expand large
retained occurrence and alignment products even when their values are abstract.
Represent an existing member/cache ownership boundary by its named record
when its original dependent tuple causes this expansion. Keep the same whole
payloads, defining equations and construction calls. A recursively indexed
observation family at a transported path can otherwise force code emission
to expand the complete endpoint-owner cast and scalar arithmetic. Retain the
whole indexed observation and its original transport factory in that cache.
Separate a retained source-completion cache from the execution indexed by
its extracted roots. Keep the whole completion and root factory in their
own fields, and index numerical execution by the same certified root value.
This avoids carrying the complete occurrence product through every numerical
getter while preserving the original input objects and producer calls.

Use the existing named
field types during record and injectivity generation, then restore ordinary
client reduction. Generated projections may have different reducibility from
authored getters; remove obsolete local attributes instead of overriding
validation. Verify complete code emission and the actual cache argument flow.

If a long callback application exhausts conversion, isolate the cost of its
successive argument groups. A single raw comparison can unfold retained model
factories and polynomial evaluations for each application. Name that exact
proposition at its existing mathematical owner and use it in both callback
contracts. Preserve the original model, refinement depth, point and inequality;
check the complete producer and real consumers with ordinary Lean limits.

Factoring a comparison into a helper may leave expensive index inference at
its caller. Give extracted data their exact source types and pass the
original parent list, count, path, stage, Targets and owner indices explicitly.
Inferring these through a retained request or member projection can unfold
its whole dependent construction even when the helper itself checks quickly.
Use the stored indices and factories; coordinate or readback agreement does
not authorize replacing their owners.

A nested certified-cache constructor can also exhaust conversion at its last
reflexivity proof after earlier field inference has spent the budget. Give
each retained payload its exact dependent type and keep its incoming
operations locally irreducible while assembling that constructor. Restore
ordinary reduction afterward. This prevents inference from expanding the
whole Point, Entry or comparison producer without changing the cache values,
factory equations or client interface.

For a scalar maximum certified over freshly built request caches, assemble
the certified tuple in a helper taking the caches as given parameters. Then
call it after their producers run. The scalar factory checks against those
parameters without reducing the request builders, and execution still reuses
the same cached values.

Generated proof auxiliaries can make even a read-only projection expensive to
kernel-check. Name its complete parameter family, retained payload type and
bounded incidence type before declaring the projections. Check the original
reader bodies and emitted runtime functions when introducing these exact
aliases; a faster type boundary need not change the stored data or execution.

For generated heterogeneous equality helpers, compare field types under two
independent copies of the record parameters. If conversion unfolds computed
geometry or arithmetic, protect the exact aliases with local irreducibility
while generating the record and its constructor certificates, then restore
normal client reduction. Check actual constructors, projections and callers.
An exposed field readback may reduce to a projection from its representation.
If constructor-certificate reconstruction reports an invalid projection from
an opaque alias, keep that representation alias reducible during reconstruction;
protect the other expensive field aliases separately. The source declaration
and generator can need different local transparency settings. Preserve the
same readback operation and verify its actual constructors and clients.

Keep the existing injectivity API; see
[constructor certificates](constructor-certificates.md) for its generation.

When the cost is compiler dependency collection, check that the repository's
shared-node collector repair is active through `scripts/run-lake.sh`.
Changing compiler source or imported artifacts alone does not replace the
native compiler implementation. A toolchain repair must preserve the returned
dependencies as well as complete artifact emission.

## Automatic section-variable analysis

Unused-section-variable analysis can traverse theorem types, proof terms and
the types of other variables repeatedly. Look for `elabFunValues`,
`Expr.containsFVar` or `hasAnyFVar` in the profile.

Compact dependent types first. If scanning the proof remains expensive,
declare the theorem's existing parameter telescope explicitly instead of
inferring it from the surrounding section. Preserve premises, binder modes,
argument order and ownership data, then check downstream applications.
Keep the linter enabled; artificial `include` directives or unused parameters
do not repair the cause.

A theorem can spend most of its asynchronous `Elab.definition.value` time
outside the nested proof steps, while kernel checking stays cheap. Put its
complete existing telescope and conclusion in a closed `Prop` definition,
then introduce those binders explicitly in the proof. Preserve each premise
and binder mode. This also avoids repeatedly inferring a large section context;
a parameterized proposition alias leaves that context on the theorem.

## Thin wrappers and native compilation

If `Compiler` / `toMono` dominates a forwarding definition or projection,
inspect its dependent parameter types as well as its small body. Cheap
projections and single-call forwarders can use `@[expose, macro_inline]` so
clients inline them before this conversion. Keep the actual builder behind
its existing interface; do not expose proof implementations or inline an
expensive construction repeatedly.

A constructor that binds a computed owner and immediately builds a large
dependent payload can force native conversion through that owner's entire
factory. Move the payload construction into a named constructor accepting the
same retained owner as an argument. Keep that call boundary when needed, and
have the outer constructor compute the owner once before calling it. Verify
complete values, factory equations and actual cache reuse.

If `macroInline` or `transform` dominates compilation, inspect implicit
argument types and retained factory predicates as well as the small source
body. Inlining a projection can expand large cached interfaces before proof
erasure. Use exact named carrier and predicate aliases for those fields,
and retain ordinary exposed calls around large forwarding operations.
Keep the original whole-constructor equation and check complete emission of
its actual clients.

For a small finite index in a large dependent context, splitting into index
equalities and calling `subst` can repeatedly scan unrelated owner and cache
types. Use direct `Fin.cases` elimination with the original branch certificates
and an empty-index eliminator instead. This preserves exhaustive coverage
without rewriting the surrounding context. Check complete artifact emission
as well as declaration elaboration after the change.

## Control conversion through computed owners

A dependent field type that projects from a computed preparation can force
Lean to unfold that preparation repeatedly. Retain the preparation as a field
with an exact defining equality, then index later fields by that variable.
Consumers can substitute the equality once when they need the canonical form.
Apply the same technique to expensive scalar projections such as magnitudes,
counts and degree bounds.

Naming a type may be insufficient when its arguments still contain a computed
root or query factory. Define the dependent payload over the retained owner;
protect a factory from elaborator conversion locally when necessary. Builders
must still compute and consume that same original cache.

An unnecessary reflexive readback between a transparent getter and its
expanded body can itself trigger deep conversion through the cached procedure.
Keep the exposed getter when it is the required reduction API; do not add a
second law without a consumer. For a required law, prove the generic field
identity at the original abstract cache owner and specialize it afterward.

A property proof about a field deep inside a computed dependent tuple may
spend most of its kernel time converting through the whole constructor.
Prove the generic tuple/subtype projection property at its existing data
owner, then specialize it to the retained cache. Preserve the original
statement and check that executable output is unchanged.

Give projections from large certified dependent tuples explicit result types
using the retained named owners. Inferred getter types can expand the full
tuple and its nested preparation factories. Keep the original projection
bodies and use earlier getters in later result types, so the interface shares
those owner expressions without reconstructing the caches.

Deep `Sigma` projections can still duplicate the complete remaining tuple in
their dependent type arguments. Name intermediate tuple tails with exposed
`def` aliases over the same retained fields. Choose a few boundaries that keep
those arguments small, and check definitional equality with the original
product and `Sigma` type. Naming only an individual field or the getter's
result does not shorten the tail carried by each projection.

If `Meta.letToHave` unfolds an exact root or owner transport while checking
a dependent constructor, retain the whole certified pair before building
its dependent payload. Pass that pair's `.val` to the payload constructor
and return the same pair. Building from a raw `let` value and adding its
Subtype only in the final constructor can make conversion compare a
projection of a new constructor with the raw transport, unfolding its full
ownership proof. This transformation also uses full transparency, so local
irreducibility alone does not repair it. Preserve the original producer
calls and verify that the retained certified value is actually reused.

When inspecting a cached sum or option with a large dependent payload, a
direct match can force expensive conversion of its concrete owner arguments.
Use the existing generic selector, such as `Sum.getRight?`, and map its actual
stored branch into the required view. Retain the whole original parent and
negative certificate; do not replace inspection with a new checker call.
Check complete native emission to confirm that the selector consumes the
cached sum and no preparation or comparison factory is replayed.

For an indexed container whose empty case has one possible constructor, a
second match inside a dependent cache type can force endpoint transports and
large owner expressions to reduce. Add a view at the original container
owner that reads its retained payload. Let the cache's empty case use that
view while matching only its collection index. The cache type can then reduce
with an abstract or transported container, preserving the same payload and
its factory rather than reconstructing it.

Simultaneously matching two spines whose indices include computed recasts can
exhaust conversion before their branch bodies elaborate. Eliminate the
original geometric spine first with `casesOn` and an explicit motive over
its free list indices. Consume the dependent request or cache spine after
those indices are fixed. Use the same order in the recurrence proofs and
recurse only on the original retained tail. Pointwise `change` equations
avoid unfolding a whole recursive function through an equality certificate.

For a dependent finite reader, constructing the head at a concrete selector
can unfold the entire selected geometry and its scalar coordinates. Package
the complete head at an abstract retained source first. A small generic
dispatcher can then transport that whole value through the existing zero and
successor selector equations; delay recursion over the original tails. Use
the object's existing congruence law to compare dependent appends instead of
rewriting through their full ownership payload. Check whole-value readbacks
and native argument flow after this change.

Check implicit arguments too. A constructor supplied with a cached object may
still receive a computed ambient, endpoint or index through inference. Supply
the retained field and its exact equality explicitly. A certificate indexed by
an expensive computation does not itself cache the computation's value.

Substituting a retained attachment's constructor equality around an executable
action can replace its projections with fresh constructor calls. Keep the
actual attachment as the computational input and substitute the equality only
inside the refinement-law proof. Pass its retained track explicitly to state
readers and successor actions, then inspect emitted code for attachment or site
reconstruction. The proof transport should erase while the original data and
completed state entries remain the reader's inputs.

In a recursive list reader, inferred indices can call a cache-product
projection on the entire remaining tail at each head. Bind the original
head cache and pass its parents, cover and other correctness-bearing indices
explicitly. Compare emitted code: one retained head read and one tail call
should not reconstruct or traverse the whole product at every occurrence.
Proofs of equal readback alone do not establish execution reuse.

Operational comparison certificates contain executable selectors. Building one
through a canonical evaluator can replay root or expression producers even
when its equality transport erases. Compare retained construction trees using
their actual leaf annotations, and keep canonical equalities in proof
transports. Inspect emitted code for evaluator, compiler and leaf-factory
calls before accepting execution reuse.

For a result indexed by a scalar cache, retain that cache through the
construction and transport only its final index. If kernel profiling shows
that `Eq.mp (congrArg family same)` repeatedly checks a large dependent
family, use `Eq.rec` with that same family as its explicit motive. Supplying
the equal scalar expression earlier can introduce a fresh evaluation at
runtime. Check the complete emitted construction and its helper calls.

When kernel stacks show repeated expression comparison in a scalar boundary
proof, bind the retained polynomial, evaluation function and sample before
transporting endpoints. Use those same scalar bindings in the intermediate
bound and transport. This keeps large dependent cache projections out of the
repeated comparisons; verify that emitted builders retain their original
cache use.

When nanoda spends its time checking a small dependent cache constructor,
profile individual declarations on the retained graph. A reflexive readback
can force reduction of an identity transport through large cached owners.
Construct the exact transport named by the result's certificate instead,
sharing the stored equality between its value and readback. Preserve the
original comparison and its observations. Compare complete emitted functions
and recheck the whole source-root closure with the production checker.

For a theorem projecting certificates from a concrete dependent selector,
measure signature checking separately from proof checking. If the proof spends
its time comparing the selector's expanded result, prove the projection for an
arbitrary retained certificate family in a private theorem, then apply that
theorem to the original selector. This preserves its computation and witnesses
behind an opaque proof boundary. A local `let` or `generalize` can be inlined
again. Unpack dependent certificate pairs before extracting their bounds;
long projection chains can leave the helper expensive too. Inspect the retained
proof, check the helper's complete closure, and measure it in the full shared
graph as well as the scoped graph.

When projecting a field through an original owner equality, check whether the
field's result type is independent of that owner. Eliminating the owner
equality first can reduce the stored projection directly. Specializing a
generic transport lemma at a concrete acquisition may instead force repeated
checking of the whole dependent constructor. This direct readback also proves
identity of a retained executable closure without function extensionality or
replaying its acquisition.

For small adapters, use `dsimp only [AdapterDefinition]` to expose the required
head before applying a retained certificate. Reduce only that adapter. Look
for accidental repeated normalization such as `cache.normalize.normalize` when
the certificate describes a single normalization.

A direct assignment between differently headed equalities may ask the kernel
to evaluate a large canonical constructor. Prove a generic pointwise identity,
specialize it to the constructor, and compose it with the cached equality using
`Eq.trans` and `Eq.symm`. Keep the computation outside conversion. The same
technique helps when an independent checker spends much longer reducing a
proof than Lean does.

For a cache projection law, first compose existing field or factory equalities
at the same retained parameter. Proposition-valued congruence over a complete
dependent record can force conversion of unrelated geometry even when the
conclusion reads only one cache.

## Prove scalar facts before supplying large owners

Prove the smallest generic identity at the object's existing abstraction level,
then specialize it to retained data. For matrix identities, use associativity
and distributivity before expanding entries. For recursive operations, apply
the selected branch equation before transporting scalar equalities.

Move arithmetic out of large dependent contexts into private lemmas over the
few relevant scalars. Pass the retained balance equation or inequalities to
that lemma instead of asking a tactic to preprocess the whole preparation.
Split conjunctions before scalar Omega calls and clear irrelevant existential
assumptions. Prefer an existing cancellation or reflexivity law when it suffices.

For polynomial identities, use independent norm, dot-product or determinant
variables, prove the scalar identity, then supply their coordinate laws.
Use symmetric sums and products or an existing recurrence before expanding a
high-degree composition. Factor large finite case proofs into scalar row lemmas.

Apply scalar projection/readback laws before kernel decision. Deciding the
closed coefficient expression is cheaper than reducing a complete compilation,
normalization tree or geometric cache to reach those coefficients. Keep the
original owner and cache assertions in the surrounding theorem.

## Keep rewrites local

For polynomial-expression readbacks, first expose the exact scalar
numerator and denominator with `change`, then apply the owned evaluation
laws. A rewrite need not unfold opaque projections to discover their
constructor. Likewise, match an affine parameter's exact real-axis Gaussian
representation before applying a pullback readback. These repairs preserve
the cached polynomial and Point rather than exposing a whole geometric owner.


Rewriting through a dependent record can spend time in `Meta.kabstract` or
conversion. Use `congrArg`, `congrArg₂` and explicit `Eq.mpr` transport on small
equalities over the actual retained data. Avoid abstracting over the whole
geometry or cached conditional.

If stacks show `substCore` or `replaceFVar` beneath constructor-case
unification, split the finite constructor before introducing its dependent
cache arguments. Bind those arguments inside each branch, retaining the
same literal tail and induction hypothesis. This avoids substituting through
already elaborated owners and comparison records.

If branch certificates mention the original discriminator, rewriting it may
produce an ill-typed generalized goal. Split the actual match and use its
retained equation to exclude impossible branches. For dependent conditionals,
use `byCasesDec` with the original proposition and supplied decision, then
explicit `dif_pos` or `dif_neg`. Select the conditional at the value head,
rather than an unrelated one in its dependent result type.

Give shared finite predicates one definition when signatures must agree on
them. Repeating the same dependent match in separate signatures can create
distinct opaque matcher helpers whose printed propositions look identical.
For concrete readbacks, first specialize a generic projection law and only
then reduce the scalar result.

Use pointwise recursion equations instead of a generated whole-function
`eq_def` when only one application matters. Broad simplification under
functions or universal binders can add unwanted proof dependencies as well as
conversion work. Keep shared list tails and cached records out of scalar
simplification.

## Closed numeral proofs and casts

Large numeral casts may recurse through natural or integer casts. Inspect
casts inside powers, loops and fixture definitions when kernel decision or
conversion reaches the ordinary recursion limit.

Even a small closed rational comparison can be expensive when its numeral
reduces through a generic ring instance. Inspect the retained cast and decision
expressions before changing a surrounding dependent construction. Reuse a
direct cast law at the same explicit index and decide only its natural-number
premise. Compare emitted code when the repair should affect proofs alone.

For natural-cast positivity and ordering, use the owned `natCast_pos_direct`
and `natCast_le_direct` lemmas with explicit indices. For exact rational
computations, rewrite with `natCast_eq_fromInt` before kernel decision.
For Gaussian values, first apply the coordinate cast readbacks and reduce
the resulting scalar coordinates. Preserve the original target by equality
transport.

Expensive executable fixture evaluation can hide the same cast problem.
Select the owned `Fraction.Cast.fromInt` on the original integer, or on
`Int.ofNat` of the original natural, and retain the old formula through its
cast law. Raising the interpreter stack or moving evaluation to a different
backend leaves the underlying computation unchanged.

Prepared integer polynomial evaluation can still spend time normalizing its
final rational quotient. A stack passing through `Prepared.evaluate`, fraction
multiplication and integer GCD identifies that cost separately from homogeneous
integer evaluation. For a zero-decision consumer, use `Prepared.zeroDecision`
and its original evaluation witness. Check which callers need the complete
ordered evaluation cache before deferring value construction; preserve those
values and receipts for clients that consume them.

A result projection after an eager scan can still construct every stored
value. Share the indexed traversal and its actual numerator between the full
record and point-selection consumers. Put value construction inside the final
consumer, and specialize that consumer explicitly if recursion changes it;
default specialization may retain the eager path. Check the actual emitted
entry and recursive bodies: point selection should use integer zero tests,
while full-record selection must preserve every ordered value and receipt.

A point-only scan can still construct huge integer denominator powers merely
to decide nonzero. Reduce its original integer coefficient table once, outside
the point-producing function, and evaluate that retained table in bounded
residues. A nonzero residue certifies the exact numerator is nonzero; a zero
residue must run the original integer test. Any nonzero modulus works, including
one, so the screen introduces no restriction on coefficients or points. Use the
original direct signed remainder cast and its ring readback laws instead of
executing a recursive generic numerical cast.

Share the exact and residue accumulator traversal. Retain the original
numerator in a memoized `Thunk`: defer it after a successful screen, and retain
the already computed integer after fallback. Prove complete scan and cache
agreement, then inspect the actual specialized point-selection body for removal
of numerator forcing and rational-value construction. Full-record clients must
force the same cache once. Exercise zero residues with nonzero exact values,
both signs, zero denominators in the homogeneous helper and repeated native
cache reads. Compare `rational-evaluation-profile <column.json>` on the saved
original polynomial and coordinate; its time includes decoding and eliminant
construction as well as zero discrimination.

A cache equality in a recursive definition's context can make generated
equation proofs rewrite a captured cache parameter while its recursion closure
still expects the original parameter. Give that exact equality a named
proposition and make it locally irreducible only around equation generation.
Restore ordinary reduction for clients and check their actual constructors and
projections. In agreement proofs, split the retained decision itself and
transport scalar readbacks; rewriting a whole dependent pair can generalize
across an opaque generated proof with a different retained index.

Endpoint sign variation can also normalize full polynomial values that its
result never reads. Clear each original coefficient table and evaluate its
homogeneous integer numerator. The positive coefficient and point denominators
certify the same signs, including zero transitions. Retain the original exposed
rational formula, prove all-input variation agreement and check the emitted
clients use the integer implementation. Compare complete retained declaration
records when the repair should preserve the original unfolding interface.

If saved-data reloads sample inside decimal parsing and large natural
multiplication, nine-digit batching can still repeatedly multiply the entire
growing prefix. Merge equal-width decimal blocks with balanced carries instead.
Retain each block's positional factor, including leading zeroes, and prove
agreement with the scalar byte recurrence for every parser state. Preserve
separator failures, partial final blocks and signed zero. Use
`canonical_isolation_checkpoint_harness decimal-parser-profile <column.json>`
to compare both execution orders on the saved coordinate's denominator against
the sequential nine-digit reference. The runner checks complete parse results
outside the timed regions without rendering the resulting large natural.

If decoder samples reach large rational GCDs, measure scalar parsing and
normalization separately from file and JSON loading. Independent coefficient
encodings can use `Purelib.Data.Task.Parallel.mapExcept`: two contiguous halves
reuse the original scalar procedure and are joined before returning the same
ordered values or first typed error. Keep the original sequential wire decoder
as its exposed logical definition and prove complete agreement with the native
implementation. Preserve checks that precede coefficient decoding, supplied
expected-value caches and the original later certificate verifier.

Use the existing bounded task producer, with no nested parallel groups inside
its scalar jobs. A pure `let` for the second calculation does not guarantee
overlap: the compiler can move it after the first task's `get`. Inspect the
actual emitted spawn, dependency and join calls before timing. Run
`canonical_isolation_checkpoint_harness fraction-decoding-profile <column.json>`
on retained original columns to compare both execution orders and complete
results, including first-error fixtures. Its timings cover scalar parsing and
normalization, not whole checkpoint execution. Reassess complete worker memory
when adding concurrent calculations.

For saved division witnesses, use
`canonical_isolation_checkpoint_harness division-check-profile <division.json>`
to separate loading, parsing, normalization, the exact division check and
current payload rendering. It checks the same complete legacy and compact
payloads without running the old decimal-rendering baseline. Use
`division-codec-profile` when comparing that baseline on inputs small enough
to finish within the wall-clock limit.

An empty quotient in a saved division often repeats the normalized dividend as
its entire remainder. Supply that retained polynomial to the existing expected
coefficient decoder, which checks each parsed numerator and denominator before
reuse. Its complete-result law preserves unmatched encodings and first failures;
the original normalization, degree and division-identity checks still follow.

If certified UTF8 reloads sample in byte-array comparison and `Array.toList`,
check whether native execution materializes byte lists solely for equality.
The owned decision can retain its constructive kernel body while binding to
the original packed-byte runtime comparator. Verify the exact carrier, decision
ABI and borrowed-argument annotations; inspect the emitted call and temporary
buffer releases. Retain kernel fixtures alongside
native equal/unequal-byte, length, embedded-NUL and UTF8 boundary checks.
Use `json_regression --byte-array-profile FILE` on retained original input:
two independent binary reads avoid a shared-pointer shortcut, both comparison
orders are measured, and complete certified decoding is timed separately.
Keep first-use allocation separate from later rounds and use identical thread
settings. Comparator timing alone establishes no whole-reload or root speedup.

When String conversion discards the decoded character list, consume a certified
validity decision instead. Retain the decoder-backed kernel decision and prove
equality of the complete original conversion results for every input. Match the
strict native validator's borrowed-byte ABI and verify the emitted rejection
cleanup and successful construction from those same bytes. Measure complete
conversion separately from byte comparison and JSON parsing.

If JSON reloads sample inside quoted-string parsing, inspect the emitted loop
for per-character parser-result allocation and character pushes. Scan ordinary
Unicode spans at the original scalar boundaries and extract each span once.
Keep escapes on their original decoder, including surrogate rollback, and keep
control failures and end-of-input errors at their original byte offsets. Use
`json_regression --parse-profile FILE` on retained original input to measure
complete parsing separately from file reading, UTF8 conversion and decimal
decoding. Compare identical regression clients linked with the original and
repaired parser, including errors after long spans; parser timings alone do
not establish whole-checkpoint speedup.

When stable root selection samples inside `Preparation.observe` while only
requesting a coverage budget, inspect the emitted constructor projections.
An eager observation can perform a full refinement and localization merely to
return its index. Compute that index from the same retained scale and threshold;
keep sample localization in the returned callback. Preserve the complete
`CoverAt` record, including every later locator result, through its readback law.
Use `cubic_sheets_harness --localization-coverage` to calibrate the source
diagnostic: budget preparation must read no samples, while the reference
observation and actual locator must read the original source.

To reuse a completed source refinement in that locator, pass its exact scalar
and original-index readback to `Preparation.nearbyFromSample`. Retain the same
factor and root-pair caches when assembling `Selection.ofNearby`; its complete
selection equality avoids rerunning the default selector. Numerical readers
use `RootSelectionCheckpoint.Multiplicity` and the existing original-state
store. Calibrate cached locator and selection stages separately: neither may
read the source again, and a failed reader must propagate its original error
before the selection continuation runs. This source boundary does not persist
the production of factor families or pair banks; stage those producers before
launching an expensive full selection.

Repeated rational normalization inside Gaussian dot products can dominate a
matrix-column check. Clear the original operands with their least common
denominators, accumulate products over Gaussian integers, and normalize only
the final coordinates. Retain the cleared column outside the row callback so
each row consumes that same cache. The
[Gaussian matrix action](../Purelib/LinearAlgebra/Matrix/Multiplication/Gaussian.lean)
proves equality of the complete product vector; a checker must also retain its
original success values and invalid-product diagnostics.

Use `canonical_isolation_checkpoint_harness column-product-profile <column.json>`
to compare complete products in both execution orders on saved clearance-column
operands. This reads the original polynomial, parameter and ordered column;
it does not generate a root state or column proposal. A stack in `Nat.unaryCast`
through `NaturalDenominator.value` identifies coordinate conversion separately
from dot-product accumulation. Its direct integer casts and shared denominator
preserve the original coordinate quotients without recursive addition.

For Gaussian reciprocals on either coordinate axis, use the direct scalar
branches of `Canonical.preparedInverse`. Its complete equality law preserves
the original total reciprocal, including zero, without constructing and
cancelling the squared norm. Use
`canonical_isolation_checkpoint_harness prepared-inverse-profile <column.json>`
to compare it with the original norm formula on an actual saved column's
axis coordinate; the runner checks the complete resulting Gaussian record.
Keep large execution exercises in their established native test targets when
the purpose is execution rather than proof reduction. Kernel fixtures should
check the finite scalar claim through readback laws, without evaluating an
entire source construction merely to reach that claim.

## Tactic frontends repeatedly visiting expressions

If a proof-producing traversal repeatedly visits shared expression nodes,
memoize reconstruction per proof. Use keys that preserve the required binder
names and annotations, and retain original argument expressions. Choose the
traversal policy deliberately: `Expr.traverseChildren` preserves binary
children, while generic transformation helpers can flatten application spines
or open binders.

For constant replacement, skip nonconstant nodes immediately and use one
finite-map lookup per constant instead of sequential name tests at every node.
Preserve universes, argument order, certificate packaging and unsupported-case
fallbacks. Kernel-check quantified clients and generated auxiliaries after
changing reconstruction.

Before broad definitional conversion of recursive callbacks, check exact
expression equality and apply the retained pointwise equation when its head
matches. Trying reflexivity first can unfold dependent transports and the
entire recursive computation on an unsuccessful branch.

## Large dependent constructors inside recursion

Large constructor and projection expressions inside recursive branches can
make smart-unfolding equation generation expensive. Factor result construction
into small nonrecursive helpers and call those helpers from the original
recursive equations. Retain the same structural decrease, tail and certificates.
Give head readers an exact cache-type alias with an abstract tail, so checking
their projections does not expand the next parent's complete preparation.
When construction must finish the head before reading the tail, pass the
original tail as a `Unit` continuation and invoke it after the head factories.

Jointly matching two certificates indexed by the same large constructor can
also force repeated conversion of its entire dependent payload. Give one
certificate an operation that reads its fields at that known constructor,
including the exact alignment proof and original tail. Recurse on the other
certificate and consume that view. Preserve the original field owners and
tail rather than rebuilding either indexed certificate.

When a recursive reader takes one retained cache and another indexed by it,
pass their existing exact dependent pair as one recursive argument. Factor
scalar head reads and the original tail projection into small helpers, keeping
the public interface as a wrapper. This can avoid repeated conversion through
the complete dependent head. Check actual callers and complete native emission.
Source `let` order alone does not certify emitted order: pure derived work can
move across a tail callback. Inspect the emitted calls and their argument flow
when claiming execution order or reuse.

Check complete executable emission early. A direct induction or dependent
recursor can elaborate successfully while failing code generation. When a
recursive endpoint read causes that failure, retain the endpoint directly with
a trace indexed by it, and derive its readback through the trace. Compare with
existing ownership and cache records before introducing another record family.

Separate an erased indexed type family from its executable consumers when
diagnosing conversion costs. Check the input signature alone before changing
concrete recursive equations. Direct induction may check the erased family
while leaving an unsupported recursor in executable code. A shared structural
fold with an abstract dependent result family lets concrete consumers
instantiate its function result. Delay the literal tail fold explicitly when
a head worker controls tail execution, and check the emitted head, callback
and original cache arguments. Retain the original owners and ordinary limits.

When clients must reduce an indexed type family at a constructor, retain a
reducible type algebra built by direct induction or the original datatype
recursor. An ordinary imported opaque fold cannot supply that reduction.
Give the algebra an exact named function-type motive, and use an abstract
fold separately for executable value construction. Match index binder modes
explicitly: a recursor with an explicit index needs an eta-expanded motive
when the type alias takes that index implicitly. Expose only the original
type helpers required by client reduction.

For a function-valued dependent fold, specialize its equation with the exact
result family, empty value and algebra. Apply scalar congruence to the needed
readback, or congruence on the complete paired dependent tail. Rewriting the
whole dependent goal can exhaust conversion even when the executable prefix
checks and emits code quickly. Keep proof conversion and runtime recursion
as separate diagnoses.

If a dependent multiargument dispatcher fails specifically in
`Lean.Elab.WF.mkBinaryUnfoldEq`, packing its varying arguments in the dependent
tuple used by the recursion compiler can avoid the extra wrapper equation.
Use this only for that diagnosed failure, and check clients' actual unfolding
and simplification behavior.

## Large finite tables and selectors

Factor large decision trees into named certificate rows or construction bodies,
then let the selector return those values. A result-type alias alone can leave
the whole construction expanded. State known concrete widths at the data
boundary instead of repeatedly converting computed list lengths.

For a small finite sign table, split structural cases and signs, then prove the
remaining quantified Boolean table by kernel `decide`. Splitting each Boolean
into a separate tactic branch duplicates elaboration work. For generated
algebraic certificates, select the known schema in the generator instead of
trying every template through failed ring normalization in Lean. Keep exact
proof checking and reproducible generation.

Selector shape affects client conversion. Dependent `Fin.cases` can make a
concrete two-entry lookup expensive; a scalar index test can avoid that
reduction where it preserves the full contract. Conversely, primitive recursors
can leave projected numerals stuck where structural zero/successor matches
reduce. Check arbitrary-input agreement and real clients' reduction, not only
closed output values.

## Generated proof size and reference emission

Keep generated proofs as compact theorem-schema applications or readable
constructor proofs. Share application nodes only within the matching local
context, and bound lexical nesting. Avoid serializing large elaborated terms
into source merely to bypass elaboration.

If declaration checking finishes quickly but `.ilean` emission is slow, inspect
source line lengths. Reference-position conversion traverses line prefixes to
compute UTF-16 columns; many positions on a huge generated line repeat that
work. Wrap generated source deterministically at roughly 120 columns while
preserving quoted identifiers, strings and every non-whitespace token.
Distinguish source-position changes from changes to compiled declarations.

## Module boundaries and dependency fanout

Separate intrinsic module cost from refreshing its import and consumer closure.
Use narrow direct imports and an existing standalone subject target for an
interim check. Aggregate facades and optional examples can turn a small provider
build into thousands of prerequisite jobs.

Split modules at actual objects and dependency boundaries. Independent proof
families can compile as siblings; shared construction should precede them and
late adapters should follow them. Keep useful construction chains together and
avoid arbitrary one-definition modules. Change owning generators when splitting
generated sources, then check reproduction.

Give reusable modules one Lake library owner. Overlapping roots in checkpoint
libraries can create native library emission cycles despite an acyclic source
import graph. Checkpoint libraries should import reusable modules and own only
their script roots. Keep optional example libraries out of reusable facades.

More workers cannot shorten a sequential dependency chain. Measure whole-worker
memory, including imported environments, before increasing concurrency. Use the
same thread settings and comparable host load for before/after measurements.
See [linting](linting.md) and [verification](verification.md) for those tools'
separate scheduling and cache controls.

## Diagnose the build driver before blaming a proof

Repeated Lake `Task.get` / export-info backtraces with no compiler descendants
point to driver work. Stop the identified owned supervisor and descendants,
preserve completed artifacts, and retain a bounded diagnostic excerpt instead
of replaying an expanding log.

Use `scripts/run-lake.sh` so the repository's native dependency-join repair is
selected. The pinned Lake callback can synchronously await unfinished import
metadata; `scripts/toolchain/lake-export-info.patch` joins the input, import-info
and artifact jobs before constructing export metadata. The wrapper prepares a
checked native CLI under `.lake/lake-toolchain`, with installations bound to the
pinned source, patch and native inputs. Missing or damaged outputs are rebuilt;
unsupported inputs are rejected.

The repair covers native Lake CLI builds. Interpreted Lake API calls retain the
stock kernel and IR implementation. Keep native linter-provider preparation in
its established order; the patch does not deduplicate inherited diagnostics or
repair every native build race. To check the installer and native integration:

```sh
python3 -m scripts.toolchain.prepare_lake \
  --prefix .lake/core-toolchain --cache .lake/lake-toolchain
CCL_TEST_CORE_PREFIX="$PWD/.lake/core-toolchain" \
  python3 -m unittest scripts.test.toolchain.test_lake
```

For an unpatched invocation, retry the same target selection with
`LEAN_NUM_THREADS=1` and `--quiet --wfail`. This changes scheduling; quiet mode
suppresses successful informational-log replay but does not itself repair the
internal wait or log growth. Ordinary source and linter errors still require
source repairs.

An explicit `MODULE:leanArts` target can isolate kernel and IR artifact work
from later native facets. Direct file compilation through `run-lake.sh env
lean` with Lake's saved setup can also distinguish a driver failure from a
compiler failure. Preserve the setup and requested outputs, then return to the
normal complete target after diagnosis.

## Bound host-reader memory

Measure reader RSS separately during artifact binding, import-map construction
and dependency traversal. Serialized bytes, repeated decoded names and retained
expression graphs are different sources of growth. A single worker can exceed
the host budget before parallel scheduling becomes relevant.

Use bounded file pages with complete content hashes and checked file identities.
Share immutable decoded nodes across modules while keeping their pointer address
spaces separate. For axiom observations, validate each expression graph and retain
its ordered dependency names rather than keeping every decoded proof. Preserve
the complete import environment, first-owner rules and persisted axiom tables;
splitting roots into smaller environments can change those observations.

Compare complete records and ordered dependencies against the original reader,
exercise dirty-proof rejection, and test the original large input closure under
an enforced memory cap. Scheduling reservations alone do not enforce that cap.

For parallel queries, resolve the complete import environment once in the parent.
Release temporary decoder indexes after root selection and persisted-table loading.
Decode declarations in small independent workers, retaining their original bound
parts and constant identities. Construct a compact immutable dependency view and
check its full correspondence with the parent observations before sharing it.
Intern common name prefixes and edge lists; seal the backing memory file and map
it read-only. Ordinary Python object reads change reference counts and can copy
forked pages, so logical immutability alone does not establish physical sharing.

Measure aggregate cgroup memory and private worker memory; summing RSS counts
shared mappings repeatedly. Size pools from actual headroom after import loading.
Compare complete ordered results with the serial audit, and exercise corrupted
views, incomplete replies, worker crashes and cancellation.

## Keep profiling setup cheaper than the probe

Measure input discovery, hashing, copying and report writing separately from
Lean. Reuse checked `importArts` mappings or prepared input trees instead of
rebuilding a full symlink overlay for every probe. Preserve the exact module,
package, options, private imports, server/IR parts and native providers; write
diagnostic outputs separately from immutable inputs.

Use bounded structural fingerprints and shape reports for triage. Full
`repr Expr` output can expand shared nodes into enormous text; print complete
expressions only for selected small declarations. Fingerprints do not replace
exact comparisons.

Store shared manifests once, checkpoint completed rows individually or in small
batches, and write a compact aggregate at the end. Avoid repeatedly serializing
the entire growing report. Cache immutable dependency facts within a frozen
run and revalidate inputs before accepting its results.

## Reuse completed work, not just logs

For repeated original root-state loading, inspect whether the successor's
emitted code rebuilds the axis-elimination certificate. Retain the existing
`Input.Elimination` in one shared thunk outside the recursion and pass it
through every predecessor, successor and family reader. Supply already
prepared certificate data when available. Keep initial-only requests lazy,
and verify both the successor's emitted calls and actual cache forcing in a
production consumer. Preserve the original refinement policy, requests and
complete state readbacks.

For isolation replay, pass `Input.Elimination.degree` and `certificate` through
the region, seed and band readers. A certificate indexed only by
`input.eliminationDegree` can leave an executable call to
`separatedEliminationDegree`, which reconstructs both eliminants. Transport
degree indices in proofs and retain the stored bound for execution. Check the
emitted reader and its fallback calls for that original degree computation,
and verify complete isolation equality after the transport.

Use atomic incremental checkpoints for expensive build and profiling stages.
Bind each stage to its source, toolchain, options, complete dependency artifacts
and outputs. Invalidate a changed stage and its consumers while retaining
unrelated completed work. A log or final snapshot alone does not provide restart.

When identical checks are invalidated after a supervisor restart, compare the
actual worker environments. Strip launcher diagnostic IDs and per-launch cgroup
paths before execution and input binding. Keep pool-size and changing-headroom
controls in their supervisors, while retaining fixture budgets, selected case
deadlines and consumed worker configuration. Verify reuse across separate
launches and rejection after a real input change.

Check broad source invalidations for statically selected imports. Resolve literal
module names and literal `fromlist` owners explicitly; retain the conservative
whole-Python binding for genuinely dynamic code loading.

Measure metadata latency before moving a cache containing many small files to a
remote filesystem. Per-file creation, attribute updates and flushes can dominate
even when the total byte count is modest. Keep hot build/lint caches local and
back them up as one compressed archive after their writers stop; retain small
execution records and publication receipts directly on durable storage when its
atomic writes and locks have been checked. Restoring an archive still requires
normal content and artifact-currentness validation.

For nanoda, prepare the independently selected root inventory before a large
native export. Its checked cache binds the complete private import artifacts,
the ordered selected modules and the authoritative root predicate. The existing
`scripts.nanoda.worker roots` command can prepare that inventory separately
using the pipeline's exact retained group input manifest (`nanoda-inputs/*.json`)
and native cache directory. Its `native` mode checkpoints the same producer's
complete output and raw exit before coverage validation. This permits bounded
preparation, serialization, coverage and checker jobs without repeating completed
phases. Export still compares the native roots with the independent inventory
and validates complete declaration coverage; the checker still verifies the
whole stream. Prepared roots or native bytes alone establish no proof-check pass.

Measure process shutdown separately when serialization reports completion but
the owning wait has not returned. Discarding a shared expression table can
traverse millions of entries after its last output. A standalone exporter can
keep that state live until process exit, after explicitly flushing its output
streams and propagating flush errors. Check byte agreement and output-failure
handling; consumers must still wait for the raw exit and validate retained bytes.

Keep incremental checkpoint stores in durable worktree-local directories. Temporary
source prefixes are suitable for disposable probes; copy and bind inputs before
starting work that must survive temporary cleanup. Exercise interrupted-run
recovery and reject missing, changed or corrupt artifacts on reload. Bind cached
results to the actual original request and constructor, not just equal outputs
or matching filenames.

Reference shared input manifests through checked receipts rather than duplicating
them or rewriting a growing aggregate after every batch. Bind the exact request
and protocol, executable content and retained bytes separately from numerical
validity and mathematical ownership. Adopting legacy results cannot establish
historical executable provenance. Inventory linked physical checkpoint roots and
keep immutable numerical, header and diagnostic files separate from permitted
append-only profiling suffixes.

Preserve the owning wait even if progress reporting or log persistence fails.
Record the raw exit before closing streams or reading process-group/log metadata;
retain errors and reject acceptance on them. See the
[watchdog procedure](verification.md#watchdogs-and-process-ownership) for cleanup
and replacement of owned jobs.

Keep the first generation-counter snapshot unchanged during replay.
`IntegrationCheckpoint.recordCounts` preserves that file and appends the
current counters, keyed by their exact destination path, to `profile.jsonl`.
Use `loadCounts` when checking the current execution's reuse; it reads the
latest matching entry and supports legacy snapshots without journal entries.
Keep these execution diagnostics separate from mathematical checkpoint
validation. A replay's zero generated count must not overwrite the producer's
historical count.

Before replacing a driver, identify and stop its supervisor and descendants and
confirm no superseded worker remains. Serialize Lake writers and checks that
read their outputs in the same worktree. Refresh shared prerequisites once;
independent compilers need stable input snapshots and separate outputs.

For a fixture with several compilations or audits, prepare its checked Lake
environment once. Retain the selected guarded compiler, interpreter and complete
environment for the fixture's separate outputs instead of running the toolchain
preparation wrapper at every subprocess boundary. Keep the original imports,
audit modes and watchdogs; compare per-phase timings on the same worker affinity.
When an expensive live preparation serves only some regression cases, run and
checkpoint the independent cases first so their failures cannot discard that
preparation before its clients run.

For interruption regressions, prepare checked root and ownership inventories
under the procedure's exact input bindings before starting an observation timer.
Keep the export/check interruption and recovery assertions around the actual
worker phases, and verify that preparation alone creates no export or check pass.

## Align LSP workers with the checked native frontend

An upstream server can fail on a declaration that the checked build accepts
even when both use the same `LEAN_PATH`. Native elaborator replacements belong
to the executable, not just its imported environment. Bind server and worker
executable contents, native archives/providers, compiler options and private
Core artifacts independently.

`run-lake.sh` selects a detached frontend prefix over the checked Core prefix.
Use that selected executable and bind its frontend receipt as well as the parent
Core receipt; the parent prefix alone does not identify the current frontend.

When the private compiler lacks server/worker dispatch, use a host with those
entry points linked against the same checked native frontend. An installed
upstream frontend is suitable only when those native inputs agree. Inspect
actual worker processes across all owning threads; checking the server alone
does not establish worker alignment. Keep complete host inputs and its recipe
in a durable worktree-local store, and verify them before reuse.

## LSP with the private Core prefix

Use reference queries to locate consumers without starting dependency builds.
When only compiled consumers are needed, inspect the retained `.ilean` LSP
reference indices first. Their `references` entries contain resolved
declaration names, usage locations and enclosing declarations, including
inferred method calls. Supplement them with the reverse source-import closure
and source searches, and identify missing or stale indices. Bind the source
and index bytes to the build being inspected. This avoids reopening a source
document merely to recover references; it does not check modified source.

Build the selected modules first. Run reference clients through
`scripts/run-lake.sh --no-build env` with the aligned server and
`LEAN_WORKER_PATH`; preserve `LEAN_SYSROOT`, `LEAN_PATH` and the source search
path. Request `dependency_build_mode="never"` and verify the actual setup
invokes `lake setup-file --no-build --no-cache`. If it omits those flags,
enforce them with a reader-local `LAKE` wrapper. An unwrapped client or stock
`lake serve` can choose another setup route and rebuild dependencies.

Finish source snapshots before starting readers. Copying `.lean` files under
the workspace while a server is live can trigger dependency watchers.
With bounded workers, open and query each document together before opening
the next. Wait for reference-index readiness, require clean diagnostics, and
reject stale imports or partial results. Bind actual declaration/field tokens,
UTF-8 spans, source bytes, reference-index artifacts and compiler inputs.
Supplement references with source searches and inferred record/field uses.

When an exhaustive migration inventory is part of the task's contract, exclude
comments and strings lexically, and capture inline constructors at their
definitions rather than at pattern-match uses. Supply both artifact and source
search paths, and verify a known cross-file caller. Report stale imports without
automatically rebuilding dependencies. These inventory bindings serve exhaustive
migrations; ordinary edits use source searches and affected-consumer checks.

Measure client startup, reference-index loading and document preparation
separately. Reuse one complete reference index across a frozen query selection,
with a deadline on each document's elaboration and continued aggregate progress
reporting. Repeated index initialization can dominate small query batches.

A recursive workspace watcher can spend substantial time traversing ignored
checkpoint stores. A frozen read-only client may replace notifications with
complete before/after source, artifact and native-input checks while holding
the shared build lock. Retain file watching for editing sessions. Measure full
compiler emission separately when judging the module build-time target.

Checkpoint completed queries individually and validate their original inputs
before reuse. Keep historical and current source batches distinct, then check
that current actual consumers are covered by the selected successful builds.
Serialize readers with artifact writers, and close the owned client process
group in `finally`.

## Evaluate the repair

Change one diagnosed cause, then compare equivalent quiet checking and complete
emission runs with the same imports, options, thread settings and dependency
state. Revert speculative changes that do not help. Check required outputs:
script execution alone need not emit every requested compiler artifact.

If a broad build was slow but isolated emission is fast, investigate competing
workloads, scheduling and dependency rebuilds before changing the declaration.
For a comparison that needs fresh project artifacts, use:

```sh
CCL_PROFILE_THRESHOLD=30 scripts/run-lake.sh --profile --cold --wfail build
```

`--cold` preserves the previous project build directory and starts with empty
project artifacts; toolchain, dependency and operating-system caches remain.
It disables cache downloads. Compare the ordinary build wall time separately
from the later diagnostic replays, using the same `LEAN_NUM_THREADS` setting.

Check actual consumers, defining equations, selected witnesses and client
reduction after a repair. Follow [AGENTS.md](../AGENTS.md) and the
[verification guide](verification.md) for the checks required by the change.
Changes to exposure, inlining or dependent type boundaries can move compilation
cost into consumers even when their sources are unchanged. Include those
affected consumers in measurements; unrelated slow modules need no profiling
or repair for this task. Use the same CPU affinity as well as thread settings,
and report timing variability rather than selecting the fastest run.
