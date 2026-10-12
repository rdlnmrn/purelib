module

import Purelib.Data.Rat.Interval.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field

import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation

import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat

/-- Multiplication by two preserves weak rational comparison.

The original factor two equals the sum of two copies of each input.
Adding the supplied weak bound to itself preserves the same rational comparison. -/
public theorem twice_le_twice {a b : Fraction.Rational} (less : a ≤ b) :
    2 * a ≤ 2 * b := by
  calc
    2 * a = a + a := by ring1
    _ ≤ b + b := add_le_add less less
    _ = 2 * b := by ring1

/-- Twice a nonnegative rational is nonnegative.

The original factor two equals the sum of two copies of the input.
Adding its supplied nonnegative bound to itself proves the doubled bound. -/
public theorem twice_nonneg {a : Fraction.Rational} (nonnegative : 0 ≤ a) :
    0 ≤ 2 * a := by
  calc
    0 = 0 + 0 := by ring1
    _ ≤ a + a := add_le_add nonnegative nonnegative
    _ = 2 * a := by ring1

/-- The square of a sum of two rationals is at most twice the sum of their squares.

The difference between the upper bound and the squared sum is the square
of the difference of the two inputs, which is nonnegative in the rational order. -/
public theorem add_sq_le_two (a b : Fraction.Rational) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a - b) ^ 2 := Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 := by ring1

/-- The squared dot product of two rational coordinate pairs is bounded by the product of their squared lengths.

The difference between the product of square sums and the squared dot product
is the square of the corresponding determinant. Nonnegativity of that same
rational square proves the inequality for the four original coordinates. -/
public theorem dot_sq_le_product_sums
    (a b u v : Fraction.Rational) :
    (a * u + b * v) ^ 2 ≤
      (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a * v - b * u) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) -
        (a * u + b * v) ^ 2 := by ring1

end Purelib.Data.Rat.Bounds.Square

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section
@[expose] public section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

namespace Purelib.CCL.Boundary.BoxSign

end Purelib.CCL.Boundary.BoxSign

end

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section
@[expose] public section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

namespace Purelib.Data.Rat.Bounds.Square.Boundary

open Purelib.Data.Rat in
/-- The square of a sum of three rationals is at most three times the sum of their squares.

The upper bound minus the squared sum is the sum of the three pairwise difference squares, each nonnegative in the
concrete rational order. -/
public theorem add_sq_le_three (first second third : Fraction.Rational)
  :
    (first + second + third) ^ 2 ≤
      3 * (first ^ 2 + second ^ 2 + third ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  have firstSecond : 0 ≤ (first - second) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have firstThird : 0 ≤ (first - third) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have secondThird : 0 ≤ (second - third) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    0 ≤ (first - second) ^ 2 + (first - third) ^ 2 +
        (second - third) ^ 2 :=
      add_nonneg (add_nonneg firstSecond firstThird) secondThird
    _ = 3 * (first ^ 2 + second ^ 2 + third ^ 2) -
        (first + second + third) ^ 2 := by
      ring1

end Purelib.Data.Rat.Bounds.Square.Boundary

end

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- The rational square of a nonzero integer cast is strictly positive. -/
theorem integer_square_positive (a : Int) (nonzero : a ≠ 0) :
    (0 : Fraction.Rational) < (a : Fraction.Rational) ^ 2 := by
  have castNonzero : (a : Fraction.Rational) ≠ 0 := fun equal =>
    nonzero (Fraction.Cast.Compatibility.intCast_injective_direct equal)
  have nonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct (a : Fraction.Rational)
  exact ⟨nonnegative, fun reverse => castNonzero
    ((Fraction.Order.Arithmetic.sq_eq_zero_direct (a : Fraction.Rational)).mp
      (le_antisymm reverse nonnegative))⟩
end Purelib.Data.Rat.Bounds.Square

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- The squared dot product of two rational coordinate pairs is bounded by the product of their squared lengths.

The difference between the product of square sums and the squared dot product is the square of the corresponding
determinant. Nonnegativity of that rational square proves the inequality directly. -/
public theorem cauchy (a b c d : Fraction.Rational) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a * d - b * c) ^ 2 := Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = _ := by ring1

end Purelib.Data.Rat.Bounds.Square

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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- The square of a nonzero rational is strictly positive. -/
private theorem coordinate_sq_pos_of_ne_zero {value : Fraction.Rational}
    (nonzero : value ≠ 0) : 0 < value ^ 2 := by
  have squareNonzero : value ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((Fraction.Order.Arithmetic.sq_eq_zero_direct value).mp zero)
  exact lt_of_le_of_ne (Fraction.Order.Arithmetic.sq_nonneg_direct value)
    (Ne.symm squareNonzero)
end Purelib.Data.Rat.Bounds.Square

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- The squared determinant of two rational coordinate pairs is bounded by the product of their squared lengths.

The difference between the product of square sums and the squared determinant is the square of the corresponding dot
product. The bound follows from concrete rational square nonnegativity. -/
theorem cross_sq_le_product_sums
    (a b da db : Fraction.Rational) :
    (a * db - b * da) ^ 2 ≤
      (a ^ 2 + b ^ 2) * (da ^ 2 + db ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a * da + b * db) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (da ^ 2 + db ^ 2) -
        (a * db - b * da) ^ 2 := by ring1
end Purelib.Data.Rat.Bounds.Square

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- A rational with square below the square of a nonnegative upper endpoint is strictly below that endpoint. -/
theorem lt_of_sq_lt_sq_of_nonneg {a b : Fraction.Rational}
    (bNonnegative : 0 ≤ b)
    (squares : a ^ 2 < b ^ 2) : a < b := by
  rcases lt_trichotomy a b with less | rfl | greater
  · exact less
  · exact (lt_irrefl _ squares).elim
  · by_cases bZero : b = 0
    · subst b
      exact ((not_lt_of_ge
        (Fraction.Order.Arithmetic.sq_nonneg_direct a)) squares).elim
    · have bPositive : 0 < b := lt_of_le_of_ne bNonnegative (Ne.symm bZero)
      have aPositive : 0 < a := bPositive.trans greater
      have first : b * b < a * b :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          greater bPositive
      have second : a * b < a * a :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          aPositive greater
      have reverse : b ^ 2 < a ^ 2 := by
        simpa only [pow_two] using first.trans second
      exact (lt_asymm squares reverse).elim
end Purelib.Data.Rat.Bounds.Square

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- A strict comparison after multiplication by two gives the original rational comparison. -/
theorem lt_of_two_mul_lt_two_mul_direct {a b : Fraction.Rational}
    (scaled : 2 * a < 2 * b) : a < b := by
  rcases lt_trichotomy a b with less | rfl | greater
  · exact less
  · exact (lt_irrefl _ scaled).elim
  · have reverse : 2 * b < 2 * a :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide) greater
    exact (lt_asymm scaled reverse).elim
end Purelib.Data.Rat.Bounds.Square

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section
@[expose] public section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- A square bound by a nonnegative rational radius gives both signed coordinate bounds.

The supplied nonnegative radius fixes the order of the two endpoints. Comparing the squares of the value and its
negation yields containment in the closed interval without introducing a square-root operation. -/
theorem signed_bounds_of_sq_le_sq
    {value radius : Fraction.Rational} (radiusNonnegative : 0 ≤ radius)
    (squareBound : value ^ 2 ≤ radius ^ 2) :
    -radius ≤ value ∧ value ≤ radius := by
  by_cases valueNonnegative : 0 ≤ value
  · exact
      ⟨(by
          have radiusNonpositive :=
            Fraction.Order.Arithmetic.neg_le_neg_direct radiusNonnegative
          rw [neg_zero] at radiusNonpositive
          exact radiusNonpositive.trans valueNonnegative),
        Fraction.Order.Arithmetic.nonnegative_le_of_sq_le_sq radiusNonnegative squareBound⟩
  · have valueNonpositive : value ≤ 0 := le_of_not_ge valueNonnegative
    have negativeSquareBound : (-value) ^ 2 ≤ radius ^ 2 := by
      calc
        (-value) ^ 2 = value ^ 2 := by ring1
        _ ≤ radius ^ 2 := squareBound
    have negativeLe := Fraction.Order.Arithmetic.nonnegative_le_of_sq_le_sq radiusNonnegative
      negativeSquareBound
    have lower := Fraction.Order.Arithmetic.neg_le_neg_direct negativeLe
    exact ⟨by simpa only [neg_neg] using lower,
      valueNonpositive.trans radiusNonnegative⟩
end Purelib.Data.Rat.Bounds.Square

end

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section
@[expose] public section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- The square of a sum of two rationals is at most twice the sum of their squares.

The difference between the upper bound and the squared sum is the square
of the difference of the two inputs, which is nonnegative in the rational order. -/
theorem sq_add_le_two (a b : Fraction.Rational) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have nonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct (a - b)
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a - b) ^ 2 := nonnegative
    _ = 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 := by ring1
end Purelib.Data.Rat.Bounds.Square

end

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section
@[expose] public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- Two weak signed bounds on a rational imply the corresponding square bound. -/
public theorem sq_le_sq_of_bounds {value bound : Fraction.Rational}
    (lower : -bound ≤ value) (upper : value ≤ bound) :
    value ^ 2 ≤ bound ^ 2 := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (bound - value) * (bound + value) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sub_nonneg_direct upper)
        (by
          have shifted :=
            Fraction.Order.Arithmetic.add_le_add_right_direct lower bound
          calc
            0 = -bound + bound := by ring1
            _ ≤ value + bound := shifted
            _ = bound + value := by ring1)
    _ = bound ^ 2 - value ^ 2 := by ring1

end Purelib.Data.Rat.Bounds.Square

end

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- A rational between a radius and its negation has square at most the radius square. -/
public theorem square_le_of_two_sided
    {value radius : Fraction.Rational}
    (lower : -radius ≤ value) (upper : value ≤ radius) :
    value ^ 2 ≤ radius ^ 2 := by
  have first : 0 ≤ radius - value :=
    Fraction.Order.Arithmetic.sub_nonneg_direct upper
  have second : 0 ≤ radius + value := by
    calc
      0 = radius + -radius := by ring1
      _ ≤ radius + value := add_le_add_right lower radius
  have differenceNonnegative : 0 ≤ radius ^ 2 - value ^ 2 := by
    calc
      0 ≤ (radius - value) * (radius + value) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct first second
      _ = radius ^ 2 - value ^ 2 := by ring1
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := -(value ^ 2))
  calc
    value ^ 2 + -(value ^ 2) = 0 := by ring1
    _ ≤ radius ^ 2 - value ^ 2 := differenceNonnegative
    _ = radius ^ 2 + -(value ^ 2) := by ring1

end Purelib.Data.Rat.Bounds.Square

end

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section
section
@[expose] public section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- A rational at most the negative of a positive gap has square at least the gap square. -/
theorem square_lower_of_negative {gap height : Fraction.Rational} (positive : 0 <
  gap) (upper : height ≤ -gap) :
    gap ^ 2 ≤ height ^ 2 := by
  have lower : gap ≤ -height := by
    simpa only [neg_neg] using Fraction.Order.Arithmetic.neg_le_neg_direct upper
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct positive.le lower 2
  have same : (-height) ^ 2 = height ^ 2 := by ring1
  rwa [same] at square
end Purelib.Data.Rat.Bounds.Square

end

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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- A rational strictly between negative one half and one half has square strictly below one quarter. -/
public theorem square_lt_quarter {x : Fraction.Rational}
    (lower : -1 / 2 < x) (upper : x < 1 / 2) :
    x ^ 2 < 1 / 4 := by
  have leftPositive : 0 < x + 1 / 2 := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      lower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < x + 1 / 2 := shifted
  have rightPositive : 0 < 1 / 2 - x :=
    Fraction.Order.Arithmetic.sub_pos_direct upper
  apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
  calc
    0 < (x + 1 / 2) * (1 / 2 - x) :=
      Fraction.Order.Arithmetic.mul_pos_direct leftPositive rightPositive
    _ = (1 / 2 : Fraction.Rational) ^ 2 - x ^ 2 := by ring1
    _ = 1 / 4 - x ^ 2 := by
      rw [show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]

end Purelib.Data.Rat.Bounds.Square

end

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- Strict signed half bounds on a rational give a strict quarter bound on its square. -/
public theorem square_lt_quarter_of_half_bounds {value : Fraction.Rational}
    (lower : -1 / 2 < value) (upper : value < 1 / 2) :
    value ^ 2 < 1 / 4 :=
  square_lt_quarter lower upper

end Purelib.Data.Rat.Bounds.Square

end

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat in
/-- The squared sum of two coordinate products is bounded by the product of the two square sums.

The difference between the product of square sums and the squared dot product is the square of the corresponding
determinant. Nonnegativity of that rational square proves the inequality directly. -/
public theorem sum_product_sq_le_product_sums
    (a b p q : Fraction.Rational) :
    (a * p + b * q) ^ 2 ≤ (a ^ 2 + b ^ 2) * (p ^ 2 + q ^ 2) := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (a * q - b * p) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (p ^ 2 + q ^ 2) -
        (a * p + b * q) ^ 2 := by ring1

end Purelib.Data.Rat.Bounds.Square

end

/-!
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

namespace Purelib.Data.Rat.Bounds.Square

open Purelib in
open Purelib.Data.Rat in
/-- Symmetric interval bounds on a rational give the corresponding radius-square bound.

The two signed bounds imply that the product of the distances from the
endpoints is nonnegative, so the value square does not exceed the radius square. -/
public theorem symmetric_coordinate_sq_bound
    {radius value : Fraction.Rational}
    (lower : -radius ≤ value) (upper : value ≤ radius) :
    value ^ 2 ≤ radius ^ 2 := by
  exact sq_le_sq_of_bounds lower upper

end Purelib.Data.Rat.Bounds.Square

end

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section
@[expose] public section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

namespace Purelib.Geometry.Rational.Box.OutsideSide
section OutsideSide

end OutsideSide
end Purelib.Geometry.Rational.Box.OutsideSide

end

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
section CauchyEventResolution

end CauchyEventResolution
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
section CauchyEventResolution

end CauchyEventResolution
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

open Purelib.Data.Rat in
/-- The square of a nonzero rational is strictly positive. -/
private theorem sq_pos_of_ne_zero {x : Fraction.Rational} (nonzero : x ≠ 0) :
    0 < x ^ 2 := by
  have squareNonzero : x ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((Fraction.Order.Arithmetic.sq_eq_zero_direct x).mp zero)
  exact lt_of_le_of_ne (Fraction.Order.Arithmetic.sq_nonneg_direct x)
    (Ne.symm squareNonzero)
end Purelib.RootIsolation.Cauchy.Degenerate

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

namespace Purelib.RootIsolation.Cauchy.ProductCells.Turn

section Turn

open Purelib.Data.Rat in
/-- The square of a nonzero rational is strictly positive. -/
private theorem sq_pos_of_ne_zero {x : Fraction.Rational} (nonzero : x ≠ 0) :
    0 < x ^ 2 := by
  have squareNonzero : x ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((Fraction.Order.Arithmetic.sq_eq_zero_direct x).mp zero)
  exact lt_of_le_of_ne (Fraction.Order.Arithmetic.sq_nonneg_direct x)
    (Ne.symm squareNonzero)
end Turn
end Purelib.RootIsolation.Cauchy.ProductCells.Turn

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

open Purelib.Data.Rat in
/-- The square of a nonzero rational is strictly positive. -/
private theorem sq_pos_of_ne_zero {x : Fraction.Rational} (nonzero : x ≠ 0) :
    0 < x ^ 2 := by
  have squareNonzero : x ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((Fraction.Order.Arithmetic.sq_eq_zero_direct x).mp zero)
  exact lt_of_le_of_ne (Fraction.Order.Arithmetic.sq_nonneg_direct x)
    (Ne.symm squareNonzero)
end Purelib.RootIsolation.Cauchy.Resolution

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

open Purelib.Data.Rat in
/-- The self-product of a nonzero rational is strictly positive. -/
private theorem self_mul_pos_of_ne_zero
    {value : Fraction.Rational} (nonzero : value ≠ 0) : 0 < value * value := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · exact Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
      negative negative
  · exact Fraction.Order.Arithmetic.mul_pos_direct positive positive
end Purelib.RootIsolation.Sturm.CoordinateTaylor

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

end

section
section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

section

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
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
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
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
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
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

open Purelib.Data.Rat in
/-- The self-product of a nonzero rational is strictly positive. -/
private theorem self_mul_pos_of_ne_zero
    {value : Fraction.Rational} (nonzero : value ≠ 0) : 0 < value * value := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · exact Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
      negative negative
  · exact Fraction.Order.Arithmetic.mul_pos_direct positive positive
end Purelib.RootIsolation.Sturm.RootCount

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

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat

/-- A nonpositive product makes the right operand's square at most the square of the difference. -/
public theorem right_sq_le_sub_sq_of_mul_nonpos
    {left right : Fraction.Rational} (product : left * right ≤ 0) :
    right ^ 2 ≤ (left - right) ^ 2 := by
  have swapped : right * left ≤ 0 := by
    simpa only [_root_.mul_comm] using product
  have crossNonpositive : 2 * (right * left) ≤ 0 := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct swapped
        (show (0 : Fraction.Rational) ≤ 2 by decide)
    simpa only [Fraction.Field.mul_zero_direct] using scaled
  have extraNonnegative : 0 ≤ left ^ 2 - 2 * (right * left) :=
    Fraction.Order.Arithmetic.sub_nonneg_direct
      (crossNonpositive.trans
        (Fraction.Order.Arithmetic.sq_nonneg_direct left))
  have enlarged :=
    Fraction.Order.Arithmetic.add_le_add_right_direct extraNonnegative
      (right ^ 2)
  calc
    right ^ 2 ≤ right ^ 2 + (left ^ 2 - 2 * (right * left)) := by
      calc
        right ^ 2 ≤ (left ^ 2 - 2 * (right * left)) + right ^ 2 := by
          simpa only [_root_.zero_add] using enlarged
        _ = right ^ 2 + (left ^ 2 - 2 * (right * left)) := _root_.add_comm _ _
    _ = (left - right) ^ 2 := by ring1

/-- Squaring preserves weak comparison between nonnegative rationals. -/
public theorem sq_le_sq_of_nonneg
    {left right : Fraction.Rational} (order : left ≤ right)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    left ^ 2 ≤ right ^ 2 := by
  rw [pow_two, pow_two]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct order order
    leftNonnegative rightNonnegative

/-- When two rationals have nonpositive product, the square of the left is bounded by the square of their difference. -/
public theorem
  left_sq_le_sub_sq_of_mul_nonpos
    {left right : Fraction.Rational} (product : left * right ≤ 0) :
    left ^ 2 ≤ (left - right) ^ 2 := by
  have crossNonpositive : 2 * (left * right) ≤ 0 := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product
        (show (0 : Fraction.Rational) ≤ 2 by decide)
    simpa only [Fraction.Field.mul_zero_direct] using scaled
  have extraNonnegative : 0 ≤ right ^ 2 - 2 * (left * right) :=
    Fraction.Order.Arithmetic.sub_nonneg_direct
      (crossNonpositive.trans
        (Fraction.Order.Arithmetic.sq_nonneg_direct right))
  have enlarged :=
    Fraction.Order.Arithmetic.add_le_add_right_direct extraNonnegative
      (left ^ 2)
  calc
    left ^ 2 ≤ left ^ 2 + (right ^ 2 - 2 * (left * right)) := by
      calc
        _ ≤ (right ^ 2 - 2 * (left * right)) + left ^ 2 := by
          simpa only [Fraction.Field.zero_add] using enlarged
        _ = _ := _root_.add_comm _ _
    _ = (left - right) ^ 2 := by ring1

end Purelib.Data.Rat.Bounds.Square

namespace Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat

/-- The sum of two rational squares is positive when at least one coordinate is nonzero. -/
public theorem sum_sq_pos_of_ne_zero {A B : Fraction.Rational}
    (nonzero : A ≠ 0 ∨ B ≠ 0) : 0 < A ^ 2 + B ^ 2 := by
  rcases nonzero with ANonzero | BNonzero
  · have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      (Fraction.Order.Arithmetic.exact_rational_sq_pos ANonzero) (B ^ 2)
    have lower := Fraction.Order.Arithmetic.sq_nonneg_direct B
    exact lower.trans_lt (by
      simpa only [zero_add, add_zero, add_comm] using shifted)
  · have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (Fraction.Order.Arithmetic.exact_rational_sq_pos BNonzero) (A ^ 2)
    have lower := Fraction.Order.Arithmetic.sq_nonneg_direct A
    exact lower.trans_lt (by simpa only [add_zero] using shifted)

end Purelib.Data.Rat.Bounds.Square

section

namespace Purelib.Data.Rat.Bounds.Square
/-- The square of the smaller of two rationals satisfies any common upper bound on their squares.

The original decidable endpoint comparison selects one input. Its
supplied square bound proves the common ceiling in that same branch. -/
public theorem min_sq_le {left right bound : Purelib.Data.Rat.Fraction.Rational}
    (leftBound : left ^ 2 ≤ bound) (rightBound : right ^ 2 ≤ bound) :
    min left right ^ 2 ≤ bound := by
  change (if left ≤ right then left else right) ^ 2 ≤ bound
  by_cases ordered : left ≤ right
  · rw [if_pos ordered]
    exact leftBound
  · rw [if_neg ordered]
    exact rightBound

/-- The square of the larger of two rationals satisfies any common upper bound on their squares.

The original decidable endpoint comparison selects one input. Its
supplied square bound proves the common ceiling in that same branch. -/
public theorem max_sq_le {left right bound : Purelib.Data.Rat.Fraction.Rational}
    (leftBound : left ^ 2 ≤ bound) (rightBound : right ^ 2 ≤ bound) :
    max left right ^ 2 ≤ bound := by
  change (if left ≤ right then right else left) ^ 2 ≤ bound
  by_cases ordered : left ≤ right
  · rw [if_pos ordered]
    exact rightBound
  · rw [if_neg ordered]
    exact leftBound

/-- A coordinate beyond a positive radius forces the squared norm above the squared radius.

Strict multiplication compares the positive coordinate squares; the other
coordinate contributes its nonnegative square. -/
public theorem radius_sq_lt_normSq_of_lt
    {radius x y : Purelib.Data.Rat.Fraction.Rational} (radiusPositive : 0 < radius)
    (outside : radius < x) :
    radius ^ 2 < x ^ 2 + y ^ 2 := by
  have xPositive : 0 < x := radiusPositive.trans outside
  have first : radius * radius < radius * x :=
    Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      radiusPositive outside
  have second : radius * x < x * x :=
    Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct outside xPositive
  calc
    radius ^ 2 < x ^ 2 := by
      simpa only [pow_two] using first.trans second
    _ ≤ x ^ 2 + y ^ 2 :=
      le_add_of_nonneg_right (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct y)
end Purelib.Data.Rat.Bounds.Square
end
