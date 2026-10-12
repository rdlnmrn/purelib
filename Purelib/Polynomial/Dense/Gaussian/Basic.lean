module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Basic

public import Purelib.Data.Gaussian.Field

open Purelib.Data

open Purelib.Polynomial

section

section
@[expose] public section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients
/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev CoefficientPolynomial :=
  Dense.Basic.DensePolynomial Gaussian.Basic.Canonical

end Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients

end

/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.CCL.Progressive.PolynomialRoots
end Purelib.CCL.Progressive.PolynomialRoots

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.CCL.Progressive.PowerMonodromy
end Purelib.CCL.Progressive.PowerMonodromy

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExactPolynomialLoops

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial

end Purelib.Polynomial.Dense.Gaussian.Basic.ExactPolynomialLoops

end

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreConnectors

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreConnectors

end

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section
@[expose] public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreFrame

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreFrame

end

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section
@[expose] public section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreOneLoop

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreOneLoop

end

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section
@[expose] public section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendrePreparedData
/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendrePreparedData

end

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section
@[expose] public section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendrePreparedPeriods

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendrePreparedPeriods

end

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section
@[expose] public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreSegment

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreSegment

end

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section
@[expose] public section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreZeroLoop

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial
end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendreZeroLoop

end

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section
@[expose] public section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitQuarticPreparedHorizontalCells

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev
  HorizontalGaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial

end Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitQuarticPreparedHorizontalCells

end

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Basic.GaussianCanonical
/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev CoefficientPolynomial := Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical
end Purelib.Polynomial.Dense.Gaussian.Basic.GaussianCanonical

end

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section
@[expose] public section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic
/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  Dense.Basic.DensePolynomial Gaussian.Basic.Canonical

end Purelib.Polynomial.Dense.Gaussian.Basic

end

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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

/-!
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

section
@[expose] public section

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic.PolynomialBraid

/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev GaussianPolynomial :=
  CanonicalCoefficients.CoefficientPolynomial

end Purelib.Polynomial.Dense.Gaussian.Basic.PolynomialBraid

end

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section
@[expose] public section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

namespace Purelib.CCL.Adapters.General

end Purelib.CCL.Adapters.General

end

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section
@[expose] public section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

namespace Purelib.CCL.Adapters.Polynomial
end Purelib.CCL.Adapters.Polynomial

end

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section
@[expose] public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

namespace Purelib.CCL.Adapters.ProjectiveRationalEvaluation
end Purelib.CCL.Adapters.ProjectiveRationalEvaluation

end

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.CCL.Adapters.Rational

end Purelib.CCL.Adapters.Rational

end

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section
@[expose] public section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

namespace Purelib.Polynomial.DerivativeSeparation
end Purelib.Polynomial.DerivativeSeparation

end

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section
@[expose] public section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

namespace Purelib.Polynomial.Squarefree.Evaluation
end Purelib.Polynomial.Squarefree.Evaluation

end

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section
section
@[expose] public section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

namespace Purelib.Polynomial.Irreducible

end Purelib.Polynomial.Irreducible

end

end

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.CCL.Progressive.Monodromy
end Purelib.CCL.Progressive.Monodromy

end

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Riemann.Curves.AlgebraicDifferentials

end Purelib.Riemann.Curves.AlgebraicDifferentials

end

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Riemann.Periods.LegendrePeriodJets

end Purelib.Riemann.Periods.LegendrePeriodJets

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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section
@[expose] public section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

namespace Purelib.Riemann.Integration.LegendrePicardFuchs
end Purelib.Riemann.Integration.LegendrePicardFuchs

end

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section
@[expose] public section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
-/

namespace Purelib.CCL.Progressive.PolynomialRootRelation

end Purelib.CCL.Progressive.PolynomialRootRelation

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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace Purelib.Polynomial.SeparatedVariables
end Purelib.Polynomial.SeparatedVariables

end

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace Purelib.Polynomial.SeparatedVariables
end Purelib.Polynomial.SeparatedVariables

end

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
end Purelib.CCL.Transcendental.RootPowers

end

/-!
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic

/-! ## The displayed Legendre value/derivative specifications -/

/-- The constant-one Gaussian polynomial with coefficient list `[1]`. -/
def constantOnePolynomial : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) := ⟨[1]⟩

end Purelib.Polynomial.Dense.Gaussian.Basic

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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

section

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

section

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
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
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

section
@[expose] public section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Basic

/-- The affine coordinate polynomial. -/
def coordinatePolynomial : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) := ⟨[1, 0]⟩
end Purelib.Polynomial.Dense.Gaussian.Basic

end

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Basic

/-- Remove only the finitely displayed leading zero coefficients. -/
def normalize (polynomial : GaussianCanonical.CoefficientPolynomial)
  : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := polynomial.normalize
end Purelib.Polynomial.Dense.Gaussian.Basic

end

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

end

section

section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Basic

/-- Removing displayed leading zero coefficients twice is the same as removing them once. -/
theorem normalize_idempotent (polynomial :
  GaussianCanonical.CoefficientPolynomial) :
    normalize (normalize polynomial) = normalize
      polynomial :=
  Dense.Basic.DensePolynomial.normalize_normalize polynomial
end Purelib.Polynomial.Dense.Gaussian.Basic

end

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
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
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
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
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

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

namespace Purelib.Polynomial.Dense.Gaussian
/-- Dense polynomials over canonical Gaussian rationals, with descending coefficient lists. -/
abbrev NormalizedPolynomial :=
  Dense.Basic.DensePolynomial Gaussian.Basic.Number
end Purelib.Polynomial.Dense.Gaussian

end
