# Purelib library layout and dependency boundary

`Purelib/` contains the project-owned reusable Lean library. Its modules use
the `Purelib.*` prefix; uppercase `Mathlib.*` names remain modules from the
pinned upstream dependency. New reusable code belongs under the narrowest
semantic owner in this tree, such as `Data`, `Algebra`, `LinearAlgebra`,
`NumberTheory`, `Geometry`, `Polynomial`, `RootIsolation`, or
`RationalFunctions`.

The library retains the development's executable finite boundary. Definitions
and proofs must use explicit finite data, constructive witnesses, and checked
certificates. They must not introduce classical choice, noncomputable
constructions, choice-derived enumeration, or proof routes through infinite or
completed objects. Imports from upstream Mathlib require the same dependency
and axiom audit as before; an ordinary-looking algebraic theorem is not enough
to establish that its proof route is admissible. The authoritative axiom audit
and independent nanoda check require empty transitive axiom closures for their
selected mathematical declarations, including private and generated proof
dependencies. Neither propositional extensionality (`propext`) nor quotient
soundness (`Quot.sound`) is permitted in those closures. Independent compiler
and elaborator helper coverage remains the separate strict-audit obligation
described in the [repository README](../README.md#building-and-checking).

Constructor injectivity certificates retain their original owners, arguments,
and field equalities, but express the logical characterization with `↔` rather
than equality of propositions. Direct injectivity implications remain
available. Consume equivalences with `.mp` and `.mpr`; a simplifier registration
can generate a proposition-equality companion that reintroduces `propext`.
Executable equality procedures and finite constructions retain their data and
defining equations; the logical certificate type is the API change.

The reusable foundation includes:

- explicit fields, normalized rational fractions, Gaussian arithmetic, and
  reduction-aware working representations under `Purelib/Algebra` and
  `Purelib/Data`;
- executable dense and multivariate polynomial arithmetic, root candidates,
  derivatives, division, gcd, composition, parity, and normalized resources
  under `Purelib/Algebra` and `Purelib/Polynomial`;
- structural vectors, matrices, polynomial matrices, alternating pairings,
  norms, and spans under `Purelib/LinearAlgebra`;
- explicit prime, parity, totient, binomial, quadratic, and sum-of-squares
  constructions under `Purelib/NumberTheory`; and
- domain algorithms and certified interfaces under `Purelib/Polynomial`,
  `Purelib/RootIsolation`, and `Purelib/RationalFunctions`.

Place sources and declarations under their mathematical owners and update all
affected consumers together. Preserve Lean module acyclicity and publication
coverage. Imports and proof dependencies must remain constructive and finite
under the restrictions above and the [repository instructions](../AGENTS.md).

Regression-only declarations belong under `Test/`; generated examples
and mathematical demonstrations belong under `Purelib/Examples/`; command-line
harnesses and generators remain under `scripts/`.
