# Local finite Mathlib replacements

This directory contains project-owned implementations that replace broader
upstream Mathlib algebra in the active paper proofs.  Lean module names use
the lowercase prefix `mathlib.*`; upstream modules use uppercase `Mathlib.*`.
All neutral arithmetic and Paper-I declarations use the `RFAP.*` namespace;
only the CCL-specific Gaussian-integer bridge retains a `CCL.*` namespace.

The replacement boundary contains:

- `mathlib/RFAP/ExplicitField`, `ConstructiveFraction`, and
  `ConstructiveGaussian`: explicit field laws, normalized integer fractions,
  and Gaussian rationals;
- `mathlib/RFAP/NormalizedFraction` and `NormalizedGaussian`:
  reduction-aware working arithmetic with semantic erasure and finite
  component envelopes;
- `mathlib/CCL/Integral`: the displayed Gaussian-integer bridge
  used specifically by the continued-logarithm encoder;
- `mathlib/RFAP/Computable*`: executable dense polynomial arithmetic,
  derivatives, and extended gcd data;
- `mathlib/RFAP/ConstructivePolynomial*`, `ConstructiveGCD`,
  `ConstructiveFiniteNorm`, and `ConstructiveFiniteRoots`: the finite
  coefficient and root-count substrate; and
- `mathlib/RFAP/ConstructiveBivariate`, `ConstructiveFiniteMatrix`,
  `ConstructivePolynomialMatrix*`, and `ConstructiveSylvesterBezout`: the
  explicit finite separated-Sylvester and scaled-inverse replacement.

This is an organizational and dependency-audit boundary, not a claim that
every module is independent of the higher proof libraries.  In particular,
the displayed Gaussian-integer conversion and Sylvester--Bezout certificates
reuse already proved CCL/RFAP lemmas.  Lake therefore builds the directory as
the `LocalMathlib` module collection alongside `CCL` and `RFAP`.

New code belongs here only when it is a locally maintained finite replacement
for a general-purpose upstream Mathlib carrier, algorithm, or algebraic
certificate.  Domain-specific CCL parsing remains under `CCL/`; FTA/RFAP
winding and isolation proofs and their declarations remain under `RFAP/`.
