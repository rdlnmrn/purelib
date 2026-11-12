# Lean source development

[AGENTS.md](../AGENTS.md) defines repository policy. This guide covers source
techniques for implementing that policy with the checked Lean toolchain. Read
the relevant sections when changing module interfaces, namespace ownership or
proof routes. Check compiled consumers and authoritative proof closures after
changes; these techniques do not themselves establish correctness.

## Module interfaces and execution phases

Decide name visibility, body exposure, import re-export and execution phase
separately. Put `public section` before its named namespace, or close the
section before closing that namespace. Public abbreviations and instances
already expose their bodies; avoid redundant `@[expose]` attributes.

When clients must reduce a derived equality procedure, use
`deriving @[expose] DecidableEq` to expose its original generated helpers.
Set exposure at declaration time, rather than with a later attribute.
For opaque equality laws that unfold unexposed definitions, use `:= (rfl)`;
bare `:= rfl` exports definitional-equality metadata requiring exposure.

Public signatures and exposed bodies, including retained proof fields, need
public access to their owners. Verify the retained public import path in the
same execution phase. When another deliberate public dependency already
re-exports the owner, keep a caller's direct import ordinary.

In an entirely meta tool module, preserve that phase for generated recursors,
projections and match helpers too: `meta section` does not tag every auxiliary.
Check persisted phase metadata. Strict helper-closure audits are a separate,
optional scope unless explicitly requested.

For native `extern` bindings, match the carrier, result and argument ownership.
Preserve borrowed annotations and check emitted clients release temporaries.
The foundation policy for admitting project-added native implementations remains
separate from these interface requirements.

Preserve synthesized instances when narrowing imports; successful compilation
alone does not establish the same elaboration. Keep scoped and global
registrations of the same instance at the same priority: activating a scope
replaces that instance's global entry. When changing priorities while claiming
preserved operation selection, compare complete retained operation records or
functions by kernel comparison and check direct local instance precedence.

Before exposing a private theorem, inspect its complete body and check for
private declarations with the same qualified name in consumers. Public
elaboration can lose dot access to private companion laws; expose needed
originals atomically. Public signatures and exposed bodies also need publicly
accessible certificates under their original mathematical owners.

## Namespaces, openings and source moves

Keep declarations in their actual owner namespace and share dependency openings
across a file or coherent group. Prefer opening a parent and retaining a short
qualifier such as `Matrix.determinant`. One type/namespace alias can distinguish
related objects; avoid renaming their individual operations.

Absolute `_root_` qualification applies to declaration names, not ordinary
namespace commands: `namespace _root_.X` creates literal nested components.
Balance enclosing scopes before opening an actual top-level owner, retaining
the variables, options, openings and local instances it needs. Closing a
namespace deactivates local registrations; keep them in a shared enclosing
scope, using `with_weak_namespace` when the original declaration owner must be
retained. Namespace ancestry can outrank selectively opened aliases, so keep
distinguishing qualifiers for original types and instances after moves.

Selective `open` and `open ... renaming` require declarations. For a namespace
without a declaration of that name, open its parent and keep the qualifier.
Keep routes in selective openings unique across inherited namespaces and
simple openings; Lean rejects duplicate routes even when they resolve to the
same declaration. Use a longer parent qualifier where necessary.

Imports alone do not shorten references. Select repeatedly used types or open
their parent, normally once inside the file's main namespace. Reserve local
openings for isolated uses or name-resolution conflicts. Use a shared section
when a coherent group needs another opening context. Preserve selected
declarations and instances when widening scope, and check for captured local
names, implicit parameters and existing laws.

Keep necessary qualifiers in retained `variable` binder syntax: Lean
re-elaborates it under later openings. For same-named Core replacements, select
the owned declaration explicitly and check its audited route; literal reduction
can succeed for either operation.

Keep original qualified routes in notation expansions, which Lean retains as
implicit quotations. Source lint excludes them like explicit quotations. For
reported long namespace prefixes, use shared openings after checking declaration
body namespaces, ancestor aliases and local/type-parameter capture. See
[namespace linting](linting.md#repeated-namespace-prefixes) for the survey.

Apply declaration-route changes with syntax awareness. Preserve record field
labels, tactics, local identities, binder modes and `include` declarations;
repair method calls after owner moves. Identical declaration text does not
establish the same compiled interface: compile existing calls and check retained
parameters. Preserve tactic separators, complete location clauses and field
continuations when wrapping Lean syntax; use explicit blocks for multiline
proofs. Put `include ... in` before the declaration's doc comment.

For broad migrations, consult the [reference inventory procedure](profiling.md#lsp-with-the-private-core-prefix).
Ordinary edits need source searches and affected-consumer checks. A byte-span
inventory is useful when a migration promises exhaustive reference replacement;
it is not required for every rename. Supplement reference indices with searches
for inferred record constructions and field labels. Inspect overlapping branches
or handoffs when there is evidence that another task is changing the same API,
and pin revisions when comparing or reusing that work.

When moving an effectful branch into a state action, preserve its enclosing
early return after running the action. A return inside the action ends only that
action; check the relevant early-return modes, saved artifacts and generator
markers.

## Constructive proof techniques

Use the authoritative axiom audit to check retained dependencies, including
private and generated proofs. Source syntax alone does not establish an empty
closure. The following techniques avoid known unwanted proof routes in the
checked toolchain; consult [profiling](profiling.md) for their reduction costs.

For coefficient calculations over retained numerical records, use their readback
laws, change to a closed scalar expression, and kernel-decide that expression.
`cbv` can retain proposition-equality rules or whole-function unfolding
certificates. Use the owned `Purelib.Algebra.Ring.IntCast` laws for integer casts
in generic rings; generic cast lemmas can retain axiom-bearing derived negation
instances.

Avoid deciding large rational comparisons through recursive numeral casts. Use
the owned `natCast_pos_direct` and `natCast_le_direct` with explicit indices.
For exact closed computations, rewrite casts with `natCast_eq_fromInt` before
kernel decision. For marked canonical computations, specialize the marker's
identity law and compose it with retained equalities. Implicit conversion can
unfold the entire computation in nanoda even when Lean checks it quickly.

Use the rational `mul_nonneg_direct`, `mul_le_mul_of_nonneg_left_direct` and
`mul_le_mul_of_nonneg_right_direct` helpers mapped from
`Purelib.Data.Rat.Fraction.Compatibility`. For mixed strict/weak sum bounds, use
direct strict translation and `add_le_add_direct`. Generic ordered-ring instances
and monotonicity can introduce `Classical.choice` and `Quot.sound`. Use
`Purelib.Data.Rat.Fraction.Field.mul_pow_direct` and
`Purelib.Data.Gaussian.Power.mul_pow` for product powers; the generic `mul_pow`
proof retains proposition-equality rules.

Avoid simplification beneath functions or universal binders: it can introduce
`funext` or `forall_congr`. Unfolding recursive executables can also select a
whole-function `.eq_def` retaining `funext`; use a pointwise `change` or `rfl`
recurrence and audit its closure. Specialize quantified facts first. For finite
sums, use pointwise `sumFin_congr` and scalar transport; a local congruence
attribute on `Purelib.LinearAlgebra.sumFin_congr` is available. For cached vector
readbacks, separate definition reduction, `vectorOfFn_apply` rewrites and scalar
field simplification. In list induction, isolate the current entry by scalar
congruence before simplifying the unchanged tail.

Consume proposition equivalences with `.mp` or `.mpr`. Registering them with
`simp` can emit proposition-equality companions retaining `propext`. For reported
scalar `eq_self` routes, exclude `eq_self` and `iff_self` even with `simp only`,
then finish by `rfl` or direct scalar transport. These logical rules are among
the builtins. Reduce concrete Boolean branches with pointwise `change`;
simplifier condition equalities such as `ite_cond_eq_true` can retain `propext`.

Dependent finite matches can emit logical index-equality proofs independently
of sparse-match options. Audit generated auxiliaries and kernel-check all-input
agreement when changing executable discrimination. Prefer structural recursion
on direct subterms. For necessary well-founded recursion, supply constructive
decrease proofs and audit their auxiliaries; default termination tactics can
retain axiom-bearing simp companions. Check clients' actual unfolding and
simplification after changing a selector's shape: equal outputs alone do not
preserve reduction.

Import `Purelib.Tactic.QuotientFreeOmega` directly for `omega0` and `omega`
proofs using its quotient-free frontend. Preserve the original frontend when
narrowing imports, including automatic index-bound proofs without a written
tactic call. Check compiled proofs against the original source context and
audit an existing route before replacing it.

Split conjunction goals before applying Omega to scalar components. Compound
preprocessing can retain a classical proposition decision. Clear irrelevant
existential assumptions first; preprocessing can select witnesses through
`Exists.choose`. Confirm generated auxiliaries with the closure audit.

For reflexive comparison goals, use `rewrite` and the owned reflexivity lemma;
`rw` can close them through imported generic order instances. Supply retained
index bounds explicitly, such as `values[index.val]'index.isLt`; implicit proofs
can introduce Omega and `Quot.sound`. Use direct scalar congruence instead of
`ac_rfl`, and structural induction instead of blanket `List.map_id`.

Bind a selected typeclass value before its certificate's candidate binder:
`inferInstance` under a `Decidable` binder can select that candidate itself.

## Proof generators

Constructor injectivity certificates use `constructive_injectivity TypeName`
from datatype metadata. Preserve the original `.inj` and `.injEq` API, state
`.injEq` as an `Iff` without simp registration, and suppress default
axiom-bearing generation locally when supplying checked replacements. See
[constructor certificates](constructor-certificates.md) for the full procedure.

When reconstructing generated certificates, match complete applications and
retain their original argument expressions. Use explicit `mkAppN` arguments for
nodes containing bound variables; inference through `mkAppM` needs a matching
local context. Kernel-check quantified regressions and audit generated
auxiliaries after shared reconstruction changes. Match complete datatype
arguments when checking constructor metadata: inspecting `Parent.Child` does
not cover `Parent`.

The repository also has external generators of mathematical Lean sources:
`scripts.generators.critical_exterior_proofs` rewrites proof schemas in library
modules, and `scripts.generators.sewing` emits executable Lean regressions.
Changing their mathematical output requires checking the generated sources and
consumers, along with producer regressions. See the [verification workflow](verification.md)
and [script commands](../scripts/README.md) for the applicable checks.
