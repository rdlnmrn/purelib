# Repository agent instructions

- Do not introduce `noncomputable` definitions, declarations, sections, or
  instances.  The formalization must retain executable finite constructions.
- Do not introduce `classical` sections, tactics, local instances, or
  choice-based shortcuts.  New proofs and definitions must remain constructive.
- Prefer constructive, direct proofs with explicit witnesses over `exfalso` or
  contradiction-based arguments wherever reasonably possible.  Use proof by
  contradiction only for genuinely negative goals or when no comparably clear
  constructive proof is available.
- Prefer caching expensive executable data and calculations directly in
  structures, together with equalities or certificates tying them to their
  canonical specifications, over storing only propositions such as “the
  recomputed value satisfies this inequality.”  Downstream executable code
  should consume the cached data instead of repeating the calculation.
- Study every Mathlib import carefully before adding or retaining it, including
  the actual proof dependencies of the declarations used and their transitive
  import paths; a harmless-looking statement or module name is not sufficient
  evidence.  Do not import or use anything whose proof route, intentionally or
  accidentally, relies on any infinity: for example, an infinite carrier, an
  infinite-cardinality argument, a completed infinite object, compactness,
  completion, or infinite series.  Finite fields are the explicit exception:
  constructive finite-cardinality arguments and complete enumeration of a
  finite field or its roots are permitted when the carrier, enumeration,
  decidability, and resulting witnesses are supplied as executable data.
  This exception does not permit `classical`, `noncomputable`,
  `Fintype.ofFinite`, or any other choice-derived enumeration or witness.
  Replace broad imports with the narrowest finite algebraic dependencies that
  supply an explicitly audited result.
- Keep project-owned replacements for broad upstream Mathlib algebra under
  `mathlib/`, imported through the lowercase `mathlib.*` module prefix.  Keep
  domain-specific CCL parsing under `CCL/` and FTA/RFAP winding and isolation
  proofs under `RFAP/`; do not confuse the local lowercase prefix with
  upstream `Mathlib.*`.  Use `RFAP.*` namespaces for all active Paper-I FTA
  and rational-function declarations; do not reintroduce the former theorem
  namespace.
- Preserve the one-way paper boundary described in `README.md`: the Paper-I
  facade may use finite coefficient, Sturm, winding, and rational-box data,
  but must not import CCL encoders, parsers, cylinders, formulas, or
  persistent-prefix machinery.  No source under `RFAP/` may import or refer
  to a `CCL.*` declaration; all bridge code belongs under `CCL/` and is
  part of CCL-2.  CCL-2 code may consume the Paper-I box interface.
- Keep Lean at its ordinary elaboration limits: do not add `maxRecDepth`,
  `maxHeartbeats`, or external memory/resource safeguards to make a proof pass.
- When profiling CPU or memory usage, write a purpose-built harness that uses
  the shortest practical development iteration cycle.
- Run potentially long-lived exploratory probes under an explicit
  `timeout --signal=KILL` limit of suitable duration, and bound their memory
  consumption with `systemd-run`.  These probe safeguards are operational
  diagnostics, not permission to add resource-limit options that make a Lean
  proof or repository gate pass.
- Do not introduce new `native_decide` axioms into the dependency closure of
  the paper-facing theorems.  Prefer direct proofs or kernel `decide`; any
  existing native finite certificate is an explicit trust boundary to audit
  and reduce, not a precedent for adding another one.
- Treat `scripts/check-axioms.sh` as the authoritative repository-wide axiom
  audit and a mandatory gating check before committing.  Run it before every
  commit and do not commit while it reports a failure.  Do not create ad-hoc
  `#print axioms` probe files, whether committed, uncommitted, in the source
  tree, or in a temporary directory.  Diagnose only failures first reported by
  the automatic audit, and use `scripts/trace-axiom.sh` for that diagnosis.
- Before committing, build every changed Lean file and every repository target
  that transitively depends on a changed Lean file, with warnings treated as
  errors (for example, `lake --wfail build <affected-targets>`).  A
  repository-wide default `lake --wfail build` is required only when the
  changes affect the full tree.  All affected builds must produce no linter
  warnings.
