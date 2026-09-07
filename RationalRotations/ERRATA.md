# Rational rotations errata and proof gaps

This file records confirmed issues in the draft dated 31 August 2026 of
N. J. Wildberger's *Rational rotations of three dimensional Euclidean
space*, together with the constructive replacement used by the Lean
formalization.

## Draft-wide unresolved cross-references

Status: editorial gaps; no mathematical claim is affected.

The supplied PDF still contains literal reference placeholders rather than
resolved section or bibliography links.  They include `Section [ref]`,
`Section [anchor of a rotation]`, repeated instances of
`Section [projective rotation group]`, references of the form
`[ref: dihedron paper]` and `[ref: projective quadrances and spreads paper]`,
and bibliography item 15's `[projective universal metrical geometry paper —
title to be confirmed]`.  These should be resolved before publication.  The
coverage ledger follows the actual section and item numbers in the present
draft, so the placeholders do not create ambiguity inside the formalization.

## Section 6, Theorem 31: existence of the perpendicular direction

Status: proof gap; the theorem remains true as stated.

Definition 30 defines the spread of `c(A_v)` using a non-null vector `w`
perpendicular to `v`.  Caps include null anchor vectors: Section 5 explicitly
constructs one in Example 27, and the identity has the zero anchor.  The final
sentence of the proof of Theorem 31 justifies existence of `w` by saying that
the dot product restricted to the plane perpendicular to a **non-null** `v`
is non-degenerate.  This argument does not cover a null or zero anchor, so it
does not establish existence over the full domain of Definition 30.

The formal replacement is executable and works for every anchor over a field
of characteristic different from two.  It tests

```text
(-r, t, 0),  (-s, 0, t),  (0, -s, r).
```

Each candidate is perpendicular to `(t,r,s)`.  If one has nonzero quadrance,
it is returned.  If all three are null, their coordinate equations imply
`2t² = 0`, hence `t = 0`; the non-null vector `(1,0,0)` is then perpendicular
and is returned.  `PerpendicularNonNullWitness` caches the selected vector and
both certificates, and `perpendicularNonNullWitness` performs the selection.
`RotationAxisSpreadWitness` combines this construction with the affine-anchor
and half-turn-projector charts to cache a canonical axis, representation
certificate, perpendicular direction, and spread equation for an arbitrary
rotation.  Thus the uniform form of Theorem 31 no longer asks its caller to
select a chart.

## Section 7.2, Theorem 40: missing classification of half turns

Status: proof gap; the theorem remains true as stated.

In the half-turn branch, the proof says that a product of two perpendicular
reflections equals `σ_[v]` "by the classification of half turns in Section 4."
Section 4 defines the displayed half-turn matrix and proves its elementary
properties, but it contains no converse classification: it does not prove
that an arbitrary rotation with half spread one is a displayed half turn, nor
that fixing the same axis determines it.  The cited result is therefore
absent.  The preceding assertion that the perpendicular plane has an
orthogonal non-null basis is also not made executable there.

The formal replacement proves the missing classification in finite
coordinates.  For a rotation `ρ` with half spread one, it first proves
`tr(ρ) = -1` and

```text
(ρ - ρᵀ)² = (1 + tr(ρ))(ρ + ρᵀ - 2I) = 0.
```

An antisymmetric three-by-three matrix with square zero is then shown to be
zero using its explicit anchor vector, so `ρ` is symmetric.  Consequently

```text
P = (I + ρ)/2
```

is a symmetric idempotent with trace one and zero adjugate.  The executable
`rankOneProjectorWitness` tests the three diagonal entries of `P`, selects the
corresponding nonzero row, and caches both its non-nullness and the identity
`P = vvᵀ/Q(v)`.  This yields `ρ = σ_[v]` without a basis extension or
choice.  Given any non-null first mirror normal perpendicular to `v`, the
second is explicitly `v × v₁`; Lagrange's identity proves it non-null and
the two reflection matrices multiply to `σ_[v]`.
The bundled `twoReflectionsTheorem` consumes the same cached canonical-axis
data as the uniform spread theorem, so it does not repeat the chart decision
or perpendicular search.

## Section 9, Theorem 46: incomplete dependent-case split

Status: proof gap; the theorem remains true as stated.

The proof over the rationals first treats independent `v,u`, then says that
in the remaining case `u = λv`.  This is not an exhaustive dichotomy: when
`v = 0` and `u ≠ 0`, the pair is dependent but `u` is not a multiple of `v`.
That omitted case is elementary (`c(A₀)` is the identity), but it is not
covered by the written argument.

The formal proof does not split into independent and dependent cases and does
not transfer an identity from an infinite ordered field.  It clears the three
explicit affine denominators and verifies Euler's four-square identity and
the resulting nine matrix-coordinate identities directly over the supplied
explicit field.  This simultaneously covers zero, dependent, independent,
null, and anisotropic anchor vectors.

## Section 9, Corollary 49: missing cap-domain hypotheses

Status: statement-domain gap; the displayed law is true when all displayed
caps exist.

The corollary quantifies over `x,y ∈ F` and states only `Qxy ≠ 1`.  Definition
21 also requires each input cap to satisfy

```text
1 + Qx² ≠ 0,    1 + Qy² ≠ 0.
```

These conditions are automatic over an ordered field but not over every
field in the paper's scope.  For example, over `F₅`, take
`a = (1,0,0)`, `x = 2`, and `y = 0`.  Then `Qxy = 0 ≠ 1`, while
`Q(xa) = 4 = -1`, so `c(xA_a)` is undefined.

The formal `tangentAddition` theorem therefore takes the two input-cap
certificates and the stated tangent denominator certificate.  The
four-square denominator identity then constructs and caches the output-cap
certificate automatically.

## Section 9, Theorem 50: cap argument does not cover its stated domain

Status: proof gap; the associativity statement remains true as stated.

Definition 45's anchor product only requires `v·u ≠ 1`.  The proof of Theorem
50 instead identifies both bracketings as anchors of
`c(A_v)c(A_u)c(A_w)`.  Over a field with null vectors, one of these caps may
be undefined even though all four anchor products in the theorem exist.  A
concrete instance over `F₅` is

```text
v = (2,0,0),    u = w = (0,0,0).
```

Here `Q(v) = 4 = -1`, so `c(A_v)` is undefined, while every anchor-product
denominator in the two bracketings is `1`.

The formal replacement proves associativity before entering the cap chart.
It uses the denominator-cleared pair product

```text
(x,v)(y,u) = (xy - v·u, xu + yv - v×u)
```

and verifies its scalar and vector associativity in finite coordinates.
Normalizing only the four explicitly nonzero affine denominators gives the
stated anchor equality, without requiring any `1 + Q(v)` denominator.

## Section 9, Conjecture 52: missing nondegeneracy hypotheses

Status: false as stated; Problem 68 repeats the same issue.

The conjecture says that the anchor product and its opposite are, up to
nonzero coefficient rescaling, the only associative operations of the form

```text
(αv + βu + γ(v×u)) / (1 + δ(v·u)).
```

No nondegeneracy or group-compatibility hypotheses are imposed.  Taking
`α=1` and `β=γ=δ=0` gives the total operation `v ⋆ u = v`, which is
associative and is not a nonzero coefficient rescaling of either claimed
operation.  The constant-zero operation is another immediate counterexample.

The formalization uses five homogeneous coefficients, including the constant
denominator coefficient, so that global rescaling has an unambiguous meaning.
`CoefficientProductParameters.associativityConjecture_false` proves the
projection counterexample over every explicit field of characteristic not
two.

The repaired statement now requires the zero vector to be a two-sided
identity.  For homogeneous coefficients `(α,β,γ,ι,δ)`, this forces
`ι ≠ 0` and `α = β = ι`.  Associativity then forces `ιδ = -γ²`; conversely
those four conditions are sufficient.  The rational necessity proof tests
only the triples built from the scalars `1` and `2`, and the sufficiency proof
transports every nonzero-cross member through the explicit dilation
`v ↦ (γ/ι)v` to the opposite anchor product.  The zero-cross case is ordinary
vector addition.  This exact five-parameter equivalence is
`CoefficientProductParameters.rational_hardenedAssociativityClassification`
and its paper-facing wrapper is `problemSixtyEight_corrected`.

To ensure that the formal refutation does not depend on broadening the source
family, `NormalizedCoefficientProductParameters` separately represents the
four printed coefficients with denominator constant exactly one.
`NormalizedCoefficientProductParameters.associativityConjecture_false` and
`problemSixtyEight_normalized_false` refute that exact normalized statement;
the same left projection has coefficients `(1,0,0,0)` there.

## Section 13.3, Problem 69: notation and classification scope

Status: editorial ambiguity resolved on both readings; the finite counting
and classification clauses now have formal solutions.

The symbol whose image and kernel are requested is damaged in the supplied
PDF text layer.  From the surrounding discussion it is the quadrance-class
homomorphism `chi`, formalized as `RotationQuadranceClass.ofRotation`.  The
excluded affine cap quadric is `Q(v) = -1`, because the cap denominator is
`1 + Q(v)`; the minus sign is likewise easy to lose in text extraction.

The phrase “the parabolic classes over the null directions” does not say
whether “classes” means classification by null direction and parameter or
conjugacy orbits under `SO(3,q)`.  The formalization proves both readings.
There are `q+1` canonical projective null directions and `q-1` nonidentity
parabolics over each one.  Every half-spread-zero nonidentity rotation
computes a unique direction and nonzero parameter, and has characteristic
polynomial `(X-1)^3`.  Conversely,
`characteristicUnipotent_iff_halfSpread_eq_zero` derives half spread zero
from that pointwise characteristic identity by evaluating it only at `1`
and `-1`; the characteristic-polynomial and half-spread classifiers are
therefore equivalent without polynomial extensionality or an infinite-root
argument.  Moreover, all of these nonidentity parabolics belong to one
conjugacy orbit.  The conjugator is executable: it transports the
recovered nonzero null anchors by two non-null reflections, using an explicit
null partner in the tangent/collinear case, and cap equivariance turns that
anchor transport into matrix conjugacy.  Thus the ambiguity affects how the
answer is presented, but no longer leaves either interpretation open.

The source also asks for answers as functions of `q modulo 4`.  The
formalization retains the immediate finite certificate—either an explicit
square root of `-1` or a function rejecting every displayed candidate—and now
also proves the exact conversion.  Negation pairs the nonzero squares in the
first branch, while inversion pairs all nonzero squares except `1` in the
second, giving respectively `q = 4m + 1` and `q = 4m + 3`.  Thus the
conversion is proved from explicit finite lists and is not silently imported
from cyclicity of the multiplicative group.

## Section 13.3, Problem 71: determinant factors in the general form

Status: necessary correction to the direct Euclidean formulas; the complete
finite generalization is formalized.

For a displayed symmetric nondegenerate ternary form with matrix `M`, the
Euclidean anchor formulas cannot be copied with only `Q` and the ordinary
cross product renamed.  In the coordinate convention used by the paper's
projective quaternion model, the relevant even Clifford coordinates are

`N_M(x,u) = x² + det(M) Q_M(u)`

and

`C_M(u,v) = (u × v) adj(M) = det(M) (u ×_M v)`.

Consequently the affine cap denominator is
`1 + det(M) Q_M(u)`, not `1 + Q_M(u)`, and the affine anchor-product
denominator is `1 - det(M) B_M(u,v)`.  The product numerator is
`u + v - C_M(u,v)`.  These determinant factors disappear for the standard
Euclidean form because its displayed determinant is one, but they are
essential for other forms.  For the Minkowski matrix `diag(1,1,-1)`, the cap
denominator is `1 - Q_M(u)`; the rational anchor `(1,0,0)` is therefore on
the excluded affine quadric.

The geometric statement survives unchanged after correcting the definition:
if `p` is the trace half spread, every non-null direction perpendicular to
the recovered projective axis has spread `4p(1-p)`.  The formalization caches
such a direction for every rotation, including identity, null-axis, and
half-turn cases.  It also proves cap injectivity, affine anchor recovery away
from `p=1`, the corrected anchor-product identity, and the unconditional
projective Clifford correspondence.  No anisotropy hypothesis is required
for these results; only characteristic different from two and the finite
equality tests used by the executable constructor are explicit.

The rational split specialization now also has a complete parabolic normal
form, not merely examples in each null direction.  Starting with any
nonidentity determinant-one Minkowski isometry whose characteristic polynomial
is `(X-1)^3`, `MinkowskiClifford.parabolicClassificationOfCharacteristic`
computes a Clifford preimage, normalizes its scalar coordinate to one, proves
that its vector coordinate is a nonzero null vector, parametrizes that vector
by `(p²-q², 2pq, p²+q²)`, and returns the nonzero scalar in the corresponding
additive null-axis family.  The converse characteristic-polynomial and
zero-handedness statements are stored in the same certificate.  This is a
complete direction-and-parameter classification.  The subsequent finite
split-matrix transporter proves more: for every supplied pair of these
certificates, `MinkowskiClifford.ParabolicConjugacy.parabolicConjugacyWitness`
computes a rational special-orthogonal conjugator.  Thus all nonidentity
rational parabolics form one conjugacy class, without constructing a carrier
of rational orbits.
