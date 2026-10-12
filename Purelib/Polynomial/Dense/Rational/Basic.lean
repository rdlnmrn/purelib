module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib.Polynomial

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section
@[expose] public section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

namespace Purelib.Polynomial.Dense.Rational.Basic
/-- Descending dense polynomials over the constructive rational carrier.

This is a reducible alias of the retained coefficient-list representation, preserving its original type identity and
executable operations. -/
abbrev CoordinatePolynomial := Dense.Basic.DensePolynomial
  Fraction.Rational

end Purelib.Polynomial.Dense.Rational.Basic

end

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section
@[expose] public section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

namespace Purelib.Polynomial.Dense.Rational.Basic.Integer
/-- Descending dense polynomials over the constructive rational carrier.

This is a reducible alias of the retained coefficient-list representation, preserving its original type identity and
executable operations. -/
abbrev CoefficientPolynomial :=
  Dense.Basic.DensePolynomial Fraction.Rational

end Purelib.Polynomial.Dense.Rational.Basic.Integer

end

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section
@[expose] public section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

namespace Purelib.Polynomial.Dense.Rational.Basic.RootCandidates
/-- Descending dense polynomials over the constructive rational carrier.

This is a reducible alias of the retained coefficient-list representation, preserving its original type identity and
executable operations. -/
abbrev CoefficientPolynomial := Dense.Basic.DensePolynomial
  Fraction.Rational

end Purelib.Polynomial.Dense.Rational.Basic.RootCandidates

end

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Geometry.BoxClearance
end Purelib.Polynomial.Geometry.BoxClearance

end

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section
@[expose] public section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

namespace Purelib.RootIsolation.Cauchy.Cells
end Purelib.RootIsolation.Cauchy.Cells

end

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section
@[expose] public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.RootIsolation.Sturm.CoordinateTaylor
end Purelib.RootIsolation.Sturm.CoordinateTaylor

end

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section
@[expose] public section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

namespace Purelib.RootIsolation.Cauchy.Degenerate
end Purelib.RootIsolation.Cauchy.Degenerate

end

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section
@[expose] public section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

namespace Purelib.RootIsolation.Sturm.EventPartition
end Purelib.RootIsolation.Sturm.EventPartition

end

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section
@[expose] public section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

namespace Purelib.Polynomial.Geometry.HalfPlane
end Purelib.Polynomial.Geometry.HalfPlane

end

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

@[expose] public section

namespace Purelib.RootIsolation.Isolation.AxisSafeCuts
end Purelib.RootIsolation.Isolation.AxisSafeCuts

end

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

@[expose] public section

namespace Purelib.RootIsolation.Isolation.CalculationSize
end Purelib.RootIsolation.Isolation.CalculationSize

end

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section
@[expose] public section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

namespace Purelib.RootIsolation.Sturm.NonzeroEvent
end Purelib.RootIsolation.Sturm.NonzeroEvent

end

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section
@[expose] public section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

namespace Purelib.RootIsolation.Sturm.OneDimensional
end Purelib.RootIsolation.Sturm.OneDimensional

end

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section
@[expose] public section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

namespace Purelib.RootIsolation.Cauchy.Partition
end Purelib.RootIsolation.Cauchy.Partition

end

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section
@[expose] public section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

namespace Purelib.Polynomial.Path
end Purelib.Polynomial.Path

end

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section
@[expose] public section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

namespace Purelib.Polynomial.Geometry.PathClearance
end Purelib.Polynomial.Geometry.PathClearance

end

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section
@[expose] public section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

namespace Purelib.Polynomial.Geometry.PolynomialClearanceCover
end Purelib.Polynomial.Geometry.PolynomialClearanceCover

end

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section
@[expose] public section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

namespace Purelib.Polynomial.Geometry.PolynomialEnclosures
end Purelib.Polynomial.Geometry.PolynomialEnclosures

end

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section
@[expose] public section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

namespace Purelib.Polynomial.Geometry.PolynomialPathBounds
end Purelib.Polynomial.Geometry.PolynomialPathBounds

end

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section
@[expose] public section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

namespace Purelib.Polynomial.Geometry.PolynomialQuadraticBounds
end Purelib.Polynomial.Geometry.PolynomialQuadraticBounds

end

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section
@[expose] public section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

namespace Purelib.Polynomial.Geometry.PolynomialSampleBounds
end Purelib.Polynomial.Geometry.PolynomialSampleBounds

end

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section
@[expose] public section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

namespace Purelib.RootIsolation.Cauchy.Product
end Purelib.RootIsolation.Cauchy.Product

end

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section
@[expose] public section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

namespace Purelib.RootIsolation.Cauchy.ProductCells
end Purelib.RootIsolation.Cauchy.ProductCells

end

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section
@[expose] public section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

namespace Purelib.RationalFunctions.Winding
end Purelib.RationalFunctions.Winding

end

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section
@[expose] public section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

namespace Purelib.RootIsolation.Cauchy.Resolution
end Purelib.RootIsolation.Cauchy.Resolution

end

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.RootIsolation.Sturm.RootCount
end Purelib.RootIsolation.Sturm.RootCount

end

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section
@[expose] public section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

namespace Purelib.RootIsolation.Isolation.SafeCandidates
end Purelib.RootIsolation.Isolation.SafeCandidates

end

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section
@[expose] public section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

namespace Purelib.RootIsolation.Sturm
end Purelib.RootIsolation.Sturm

end

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.SylvesterBezout
end Purelib.Polynomial.Elimination.SylvesterBezout

end

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section
@[expose] public section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

namespace Purelib.CCL.Transcendental.RootPowerBitComplexity
end Purelib.CCL.Transcendental.RootPowerBitComplexity

end

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section
@[expose] public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

namespace Purelib.CCL.Transcendental.RootPowers

/-! ## Automatic sparse derivation of every rational candidate -/

end Purelib.CCL.Transcendental.RootPowers

end

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Winding
end Purelib.RootIsolation.Winding

end

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

section
@[expose] public section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

namespace Purelib.RootIsolation.Winding.Affine
end Purelib.RootIsolation.Winding.Affine

end

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.RootIsolation.Winding.Global
end Purelib.RootIsolation.Winding.Global

end

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.RootIsolation.Winding.Homotopy
end Purelib.RootIsolation.Winding.Homotopy

end

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.RootIsolation.Winding.Polygon
end Purelib.RootIsolation.Winding.Polygon

end

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

end

section

section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

section

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

section

/-!
# Cached finite sample/variation proposals

The existing finite Horner difference bound controls movement from the lower
endpoint of any displayed rational interval.  All executable quantities are
retained with their exact specifications.  A nonpositive proposal is only an
unsuccessful estimate, not evidence of a zero.  The only dependency is the
existing finite interval-sign algebra; no analytic limit argument is used.
-/

section

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

section

/-!
# Choice-free coordinate-axis Cauchy product cells

An identically-zero coordinate stays on a displayed axis, but the remaining
coordinate of that factor is separated from zero by the same finite
clearance certificate.  This module re-centers the three finite Cauchy event
records explicitly on such rows.  No root, ambient carrier, or polynomial
evaluation extensionality is used.
-/

section

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

section

/-!
# Local constructive Cauchy-product assembly

The analytic/event part of the product theorem need only reduce three finite
signed-remainder chains to their one-sided endpoint contributions.  This file
packages exactly that data and applies the audited finite sign table.  Product
coordinates are related by four displayed endpoint equalities, avoiding any
polynomial extensionality principle.
-/

section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

section

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

section

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

section
@[expose] public section

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

namespace Purelib.RootIsolation.Winding.Product
end Purelib.RootIsolation.Winding.Product

end

end

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.NormalizedEliminant

end Purelib.Polynomial.NormalizedEliminant

end

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.NormalizedEliminant

/-! ## The two coordinate eliminants used by safe subdivision -/

end Purelib.Polynomial.NormalizedEliminant

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.CalculationSize
end Purelib.RootIsolation.CalculationSize

end

section
@[expose] public section

/-!
# Constructive interval sign certificates

Finite Horner folds compute simultaneous square bounds for values and finite
differences.  A displayed sample whose squared value exceeds the resulting
Lipschitz margin certifies one strict sign throughout a closed constructive
interval.  No root set, compactness argument, or completed real object is
used.
-/

namespace Purelib.RootIsolation.Sturm.IntervalSign
end Purelib.RootIsolation.Sturm.IntervalSign

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.RootIsolation.Sturm.Normalized
end Purelib.RootIsolation.Sturm.Normalized

end

section
@[expose] public section

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The finite chain and index calculations use the original Sturm programs
on the same canonical rational carrier.  The resource readbacks retain their
established theorem names without executing identity coefficient maps.  The accompanying recurrence bounds every
coefficient in every chain
member from the two displayed source polynomials.
-/

namespace Purelib.Polynomial.Dense.Rational
/-- Descending dense polynomials with canonical reduced-fraction coefficients.

This is a reducible alias of the original coefficient-list representation; it carries no additional normalization
certificate for the polynomial list. -/
abbrev NormalizedPolynomial :=
  Dense.Basic.DensePolynomial Fraction.Basic.ReducedFraction

end Purelib.Polynomial.Dense.Rational

end
