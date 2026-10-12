module
import Purelib.Data.Rat.Fraction.Order.Square
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.Multiplication

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Commute
import Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat

section
section

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
open scoped Purelib.Data.Nat

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

section
@[expose] public section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian Purelib.Data.Rat.Fraction

/-- The squared rational dot product is bounded by the product of squared norms.

The difference between the product and the dot-product square is the square
of the coordinate determinant, which is nonnegative for either input sign. -/
theorem gaussian_dot_sq_le_product_normSq
    (left sum : Basic.Canonical) :
    (left.re * sum.re + left.im * sum.im) ^ 2 ≤
      Basic.normSq left * Basic.normSq sum := by
  apply Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (left.re * sum.im - left.im * sum.re) ^ 2 :=
      Order.Arithmetic.sq_nonneg_direct _
    _ = Basic.normSq left * Basic.normSq sum -
        (left.re * sum.re + left.im * sum.im) ^ 2 := by
      unfold Basic.normSq
      ring1

end Purelib.Data.Gaussian.Norm.Bounds

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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A horizontal coordinate square bounded by the radius square and a fixed vertical square give norm bounds between one
and two radius squares. -/
theorem horizontal_symmetric_norm_bounds
    {radius value height : Fraction.Rational}
    (valueSquare : value ^ 2 ≤ radius ^ 2)
    (heightSquare : height ^ 2 = radius ^ 2) :
    radius ^ 2 ≤ Basic.normSq (Components.Basic.point value height) ∧
      Basic.normSq (Components.Basic.point value height) ≤ 2 * radius ^ 2 := by
  constructor
  · change radius ^ 2 ≤ value ^ 2 + height ^ 2
    rw [heightSquare]
    calc
      radius ^ 2 = 0 + radius ^ 2 := by ring1
      _ ≤ value ^ 2 + radius ^ 2 :=
        add_le_add (Fraction.Order.Arithmetic.sq_nonneg_direct value) le_rfl
  · change value ^ 2 + height ^ 2 ≤ 2 * radius ^ 2
    rw [heightSquare]
    exact (add_le_add valueSquare le_rfl).trans_eq (by ring1)

end Purelib.Data.Gaussian.Norm.Bounds

end

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A vertical coordinate square bounded by the radius square and a fixed horizontal square give norm bounds between one
and two radius squares. -/
theorem vertical_symmetric_norm_bounds
    {radius value width : Fraction.Rational}
    (valueSquare : value ^ 2 ≤ radius ^ 2)
    (widthSquare : width ^ 2 = radius ^ 2) :
    radius ^ 2 ≤ Basic.normSq (Components.Basic.point width value) ∧
      Basic.normSq (Components.Basic.point width value) ≤ 2 * radius ^ 2 := by
  constructor
  · change radius ^ 2 ≤ width ^ 2 + value ^ 2
    rw [widthSquare]
    calc
      radius ^ 2 = radius ^ 2 + 0 := by ring1
      _ ≤ radius ^ 2 + value ^ 2 :=
        add_le_add le_rfl
          (Fraction.Order.Arithmetic.sq_nonneg_direct value)
  · change width ^ 2 + value ^ 2 ≤ 2 * radius ^ 2
    rw [widthSquare]
    exact (add_le_add le_rfl valueSquare).trans_eq (by ring1)

end Purelib.Data.Gaussian.Norm.Bounds

end

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Rat.Fraction

end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data Purelib.Algebra

/-- A squared-norm bound gives both signed bounds on each Gaussian coordinate.

The supplied radius is nonnegative, and each retained coordinate square is
bounded by its square. Rational square monotonicity gives the signed bounds. -/
theorem coordinate_bounds_of_normSq_le
    {z : Gaussian.Basic.Canonical} {r : Rat.Fraction.Rational} (nonnegative : 0 ≤ r)
    (bound : Data.Gaussian.Norm.Basic.normSq z ≤ r ^ 2) :
    -r ≤ z.re ∧ z.re ≤ r ∧ -r ≤ z.im ∧ z.im ≤ r := by
  have realSquare : z.re ^ 2 ≤ r ^ 2 := by
    calc
      z.re ^ 2 = z.re ^ 2 + 0 := by ring1
      _ ≤ z.re ^ 2 + z.im ^ 2 :=
        add_le_add (le_refl _)
          (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
      _ ≤ r ^ 2 := bound
  have imaginarySquare : z.im ^ 2 ≤ r ^ 2 := by
    calc
      z.im ^ 2 = 0 + z.im ^ 2 := by ring1
      _ ≤ z.re ^ 2 + z.im ^ 2 :=
        add_le_add (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct z.re)
          (le_refl _)
      _ ≤ r ^ 2 := bound
  have coordinateBounds : ∀ x : Rat.Fraction.Rational, x ^ 2 ≤ r ^ 2 →
      -r ≤ x ∧ x ≤ r := by
    have nonnegativeUpper : ∀ {x : Rat.Fraction.Rational}, 0 ≤ x →
        x ^ 2 ≤ r ^ 2 → x ≤ r := by
      intro x xNonnegative square
      by_cases upper : x ≤ r
      · exact upper
      · have strict : r < x := lt_of_not_ge upper
        have xPositive : 0 < x := nonnegative.trans_lt strict
        have first : r * r ≤ r * x :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            strict.le nonnegative
        have second : r * x < x * x :=
          Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            strict xPositive
        have squaresStrict : r ^ 2 < x ^ 2 := by
          rw [pow_two, pow_two]
          exact first.trans_lt second
        exact (not_lt_of_ge square squaresStrict).elim
    intro x square
    by_cases xNonnegative : 0 ≤ x
    · have negRNonpositive :=
        Rat.Fraction.Order.Arithmetic.neg_le_neg_direct nonnegative
      rw [neg_zero] at negRNonpositive
      exact ⟨negRNonpositive.trans xNonnegative,
        nonnegativeUpper xNonnegative square⟩
    · have xNonpositive : x ≤ 0 := le_of_not_ge xNonnegative
      have negXNonnegative :=
        Rat.Fraction.Order.Arithmetic.neg_le_neg_direct xNonpositive
      rw [neg_zero] at negXNonnegative
      have negSquare : (-x) ^ 2 = x ^ 2 := by
        rw [pow_two, pow_two, Ring.Multiplication.neg_mul_neg]
      have negXLe : -x ≤ r :=
        nonnegativeUpper negXNonnegative (by
          rw [negSquare]
          exact square)
      exact ⟨by
          have := Rat.Fraction.Order.Arithmetic.neg_le_neg_direct negXLe
          rw [_root_.neg_neg] at this
          exact this,
        xNonpositive.trans nonnegative⟩
  exact ⟨(coordinateBounds z.re realSquare).1,
    (coordinateBounds z.re realSquare).2,
    (coordinateBounds z.im imaginarySquare).1,
    (coordinateBounds z.im imaginarySquare).2⟩
end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Rat in
/-- Subtracting and then adding the same rational coordinate recovers the original coordinate. -/
private theorem Norm.Bounds.coordinate_sub_add_cancel (left right : Fraction.Rational) :
    left - right + right = left := by
  rw [Fraction.Arithmetic.sub_eq_add_neg_direct,
    _root_.add_assoc, neg_add_cancel,
    _root_.add_zero]
end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Rat in
/-- A rational coordinate difference splits through an intermediate coordinate. -/
private theorem Norm.Bounds.coordinate_sub_via
    (left middle right : Fraction.Rational) :
    left - right = (left - middle) + (middle - right) := by
  rw [Fraction.Arithmetic.sub_eq_add_neg_direct,
    Fraction.Arithmetic.sub_eq_add_neg_direct,
    Fraction.Arithmetic.sub_eq_add_neg_direct]
  symm
  calc
    (left + -middle) + (middle + -right) =
        left + (-middle + (middle + -right)) :=
      _root_.add_assoc _ _ _
    _ = left + ((-middle + middle) + -right) := by
      rw [_root_.add_assoc]
    _ = left + (0 + -right) := by rw [neg_add_cancel]
    _ = left + -right := by rw [_root_.zero_add]
end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section
@[expose] public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The norm of a Gaussian sum is bounded by three times the first norm plus three halves of the second. -/
theorem normSq_add_le_three_one_and_half (u v : Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (u + v) ≤
      3 * Data.Gaussian.Norm.Basic.normSq u + (3 / 2) * Data.Gaussian.Norm.Basic.normSq v := by
  let difference :=
    3 * Data.Gaussian.Norm.Basic.normSq u + (3 / 2) * Data.Gaussian.Norm.Basic.normSq v -
      Data.Gaussian.Norm.Basic.normSq (u + v)
  let scalarTwo : Basic.Canonical := ⟨2, 0⟩
  have coefficient : (2 : Fraction.Rational) * (3 / 2) = 3 := by
    calc
      (2 : Fraction.Rational) * (3 / 2) = (3 / 2) * 2 :=
        _root_.mul_comm _ _
      _ = 3 :=
        Fraction.Field.div_mul_cancel_of_ne 3 2 (by decide)
  have scaledIdentity :
      2 * difference = Data.Gaussian.Norm.Basic.normSq (scalarTwo * u - v) := by
    calc
      2 * difference =
          6 * Data.Gaussian.Norm.Basic.normSq u + (2 * (3 / 2)) * Data.Gaussian.Norm.Basic.normSq v -
            2 * Data.Gaussian.Norm.Basic.normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = 6 * Data.Gaussian.Norm.Basic.normSq u + 3 * Data.Gaussian.Norm.Basic.normSq v -
          2 * Data.Gaussian.Norm.Basic.normSq (u + v) := by
        rw [coefficient]
      _ = Data.Gaussian.Norm.Basic.normSq (scalarTwo * u - v) := by
        dsimp only [scalarTwo, Data.Gaussian.Norm.Basic.normSq]
        simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im]
        ring1
  have scaledNonnegative : 0 ≤ 2 * difference := by
    rw [scaledIdentity]
    exact Norm.Basic.normSq_nonneg _
  have differenceNonnegative : 0 ≤ difference := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (2 : Fraction.Rational)) _ (by decide)
    calc
      0 * 2 = 0 := by ring1
      _ ≤ 2 * difference := scaledNonnegative
      _ = difference * 2 := _root_.mul_comm _ _
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := -Data.Gaussian.Norm.Basic.normSq (u + v))
  calc
    Data.Gaussian.Norm.Basic.normSq (u + v) + -Data.Gaussian.Norm.Basic.normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = (3 * Data.Gaussian.Norm.Basic.normSq u + (3 / 2) * Data.Gaussian.Norm.Basic.normSq v) +
        -Data.Gaussian.Norm.Basic.normSq (u + v) := by
      dsimp only [difference]
      ring1
end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

/-- The quadrance of a Gaussian sum is bounded by twice the input quadrances.

Applying the rational square bound to each displayed coordinate and retaining
both coordinate contributions gives the bound for the original inputs. -/
theorem Norm.Bounds.normSq_add_le_two (left right : Basic.Canonical) :
    Norm.Basic.normSq (left + right) ≤
      2 * (Norm.Basic.normSq left + Norm.Basic.normSq right) := by
  change (left.re + right.re) ^ 2 + (left.im + right.im) ^ 2 ≤
    2 * ((left.re ^ 2 + left.im ^ 2) + (right.re ^ 2 + right.im ^ 2))
  calc
    (left.re + right.re) ^ 2 + (left.im + right.im) ^ 2 ≤
        2 * (left.re ^ 2 + right.re ^ 2) + 2 * (left.im ^ 2 + right.im ^ 2) :=
      Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (Purelib.Data.Rat.Bounds.Square.add_sq_le_two left.re right.re)
        (Purelib.Data.Rat.Bounds.Square.add_sq_le_two left.im right.im)
    _ = 2 * ((left.re ^ 2 + left.im ^ 2) + (right.re ^ 2 + right.im ^ 2)) := by ring1

end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A tail squared norm at most one quarter of the leading squared norm gives a quarter-leading lower bound on the full
squared norm. -/
theorem lower_of_tail (value leading :
  Basic.Canonical)
    (tail : 4 * Basic.normSq (value - leading) ≤ Basic.normSq leading) :
      Basic.normSq leading / 4 ≤ Basic.normSq value := by
  have split : value + (leading - value) = leading := by ring1
  have symmetric : Basic.normSq (leading - value) = Basic.normSq (value - leading) := by
    rw [show leading - value = -(value - leading) by ring1, Norm.Basic.normSq_neg]
  have triangle := normSq_add_le_two value (leading - value)
  rw [split, symmetric] at triangle
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct triangle (by
      decide : (0 : Fraction.Rational) ≤ 2)
  have combined : Basic.normSq leading + Basic.normSq leading ≤ 4 *
    Basic.normSq value + Basic.normSq leading := by
    calc
      _ = 2 * Basic.normSq leading := by ring1
      _ ≤ 2 * (2 * (Basic.normSq value + Basic.normSq (value - leading))) := doubled
      _ = 4 * Basic.normSq value + 4 * Basic.normSq (value - leading) := by ring1
      _ ≤ _ := add_le_add (le_refl (4 * Basic.normSq value)) tail
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
  exact (Fraction.Order.Arithmetic.le_of_add_le_add_right_direct combined).trans_eq (by ring1)

end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Half the first squared norm minus the second is a lower bound for the squared distance. -/
theorem Norm.Bounds.half_normSq_sub_le_normSq_sub (left right : Basic.Canonical) :
    Norm.Basic.normSq left / 2 - Norm.Basic.normSq right ≤ Norm.Basic.normSq (left - right)
      := by
  have bound := Norm.Bounds.normSq_add_le_two (left - right) right
  have reconstruction : left - right + right = left := by
    apply Basic.ext
    · exact Norm.Bounds.coordinate_sub_add_cancel left.re right.re
    · exact Norm.Bounds.coordinate_sub_add_cancel left.im right.im
  rw [reconstruction] at bound
  have quotientBound :
      Norm.Basic.normSq left / 2 ≤ Norm.Basic.normSq (left - right) + Norm.Basic.normSq right
        := by
    apply (Fraction.Order.Field.div_le_iff_pos
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 2) (by decide))).mpr
    calc
      Norm.Basic.normSq left ≤ 2 * (Norm.Basic.normSq (left - right) + Norm.Basic.normSq
        right) := bound
      _ = (Norm.Basic.normSq (left - right) + Norm.Basic.normSq right) * 2 :=
        _root_.mul_comm _ _
  have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
    quotientBound (-Norm.Basic.normSq right)
  calc
    Norm.Basic.normSq left / 2 - Norm.Basic.normSq right =
        Norm.Basic.normSq left / 2 + -Norm.Basic.normSq right :=
      Fraction.Arithmetic.sub_eq_add_neg_direct _ _
    _ ≤ (Norm.Basic.normSq (left - right) + Norm.Basic.normSq right) + -Norm.Basic.normSq
      right := translated
    _ = Norm.Basic.normSq (left - right) := by
      rw [_root_.add_assoc, add_neg_cancel,
        _root_.add_zero]
end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section
@[expose] public section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A positive rational parameter bounds a sum norm with weights parameter plus one and one plus its reciprocal.

The weights are one plus the positive parameter and one plus its reciprocal. No square root or auxiliary norm
representation is introduced. -/
theorem normSq_add_le_weighted (scale : Fraction.Rational)
    (scalePositive : 0 < scale) (u v : Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (u + v) ≤
      (scale + 1) * Data.Gaussian.Norm.Basic.normSq u + ((scale + 1) / scale) * Data.Gaussian.Norm.Basic.normSq v := by
  let difference :=
    (scale + 1) * Data.Gaussian.Norm.Basic.normSq u + ((scale + 1) / scale) * Data.Gaussian.Norm.Basic.normSq v -
      Data.Gaussian.Norm.Basic.normSq (u + v)
  have coefficient : scale * ((scale + 1) / scale) = scale + 1 := by
    calc
      scale * ((scale + 1) / scale) =
          ((scale + 1) / scale) * scale :=
        _root_.mul_comm _ _
      _ = scale + 1 :=
        Fraction.Field.div_mul_cancel_of_ne
          (scale + 1) scale scalePositive.ne'
  have scaledIdentity :
      scale * difference =
        (scale * u.re - v.re) ^ 2 + (scale * u.im - v.im) ^ 2 := by
    calc
      scale * difference =
          scale * (scale + 1) * Data.Gaussian.Norm.Basic.normSq u +
            (scale * ((scale + 1) / scale)) * Data.Gaussian.Norm.Basic.normSq v -
            scale * Data.Gaussian.Norm.Basic.normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = scale * (scale + 1) * Data.Gaussian.Norm.Basic.normSq u +
            (scale + 1) * Data.Gaussian.Norm.Basic.normSq v - scale * Data.Gaussian.Norm.Basic.normSq (u + v) := by
        rw [coefficient]
      _ = (scale * u.re - v.re) ^ 2 +
            (scale * u.im - v.im) ^ 2 := by
        simp only [Data.Gaussian.Norm.Basic.normSq, Basic.add_re, Basic.add_im]
        ring1
  have scaledNonnegative : 0 ≤ scale * difference := by
    rw [scaledIdentity]
    exact add_nonneg
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have differenceNonnegative : 0 ≤ difference := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := scale) _ scalePositive
    calc
      0 * scale = 0 := by ring1
      _ ≤ scale * difference := scaledNonnegative
      _ = difference * scale := _root_.mul_comm _ _
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := -Data.Gaussian.Norm.Basic.normSq (u + v))
  calc
    Data.Gaussian.Norm.Basic.normSq (u + v) + -Data.Gaussian.Norm.Basic.normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = ((scale + 1) * Data.Gaussian.Norm.Basic.normSq u +
          ((scale + 1) / scale) * Data.Gaussian.Norm.Basic.normSq v) +
        -Data.Gaussian.Norm.Basic.normSq (u + v) := by
      dsimp only [difference]
      ring1
end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Gaussian in
/-- Squared distance through an intermediate Gaussian is at most twice the sum of the two squared distances. -/
theorem Norm.Bounds.normSq_sub_le_via (left middle right : Basic.Canonical) :
    Norm.Basic.normSq (left - right) ≤
      2 * (Norm.Basic.normSq (left - middle) + Norm.Basic.normSq (middle - right)) := by
  have identity : left - right =
      (left - middle) + (middle - right) := by
    apply Basic.ext
    · exact Norm.Bounds.coordinate_sub_via left.re middle.re right.re
    · exact Norm.Bounds.coordinate_sub_via left.im middle.im right.im
  rw [identity]
  exact Norm.Bounds.normSq_add_le_two _ _

end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The squared real-coordinate dot product is bounded by the product of Gaussian squared norms. -/
theorem Norm.Bounds.projection_sq_le_normSq_mul (direction sample : Basic.Canonical) :
    (direction.re * sample.re + direction.im * sample.im) ^ 2 <=
      Norm.Basic.normSq direction * Norm.Basic.normSq sample := by
  let product := Basic.conj direction * sample
  have productReal :
      product.re = direction.re * sample.re + direction.im * sample.im := by
    simp only [product, Basic.conj, Basic.mul_re]
    ring1
  calc
    (direction.re * sample.re + direction.im * sample.im) ^ 2 =
        product.re ^ 2 := by rw [productReal]
    _ <= product.re ^ 2 + product.im ^ 2 :=
      le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.sq_nonneg_direct product.im)
    _ = Norm.Basic.normSq product := rfl
    _ = Norm.Basic.normSq direction * Norm.Basic.normSq sample := by
      dsimp only [product]
      rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_conj]

end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonnegative gap below the forward imaginary displacement has square at most the full Gaussian squared distance. -/
public theorem sq_le_normSq_sub_of_imaginary_forward
    {gap : Fraction.Rational} (gapNonnegative : 0 ≤ gap)
    {left right : Basic.Canonical} (lower : gap ≤ left.im - right.im) :
    gap ^ 2 ≤ Basic.normSq (left - right) := by
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (left.im - right.im) ^ 2 := squares
    _ = 0 + (left.im - right.im) ^ 2 := by ring1
    _ ≤ Basic.normSq (left - right) :=
      add_le_add
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (left.re - right.re))
        (le_refl _)

end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonnegative gap below the reverse imaginary displacement has square at most the full Gaussian squared distance. -/
public theorem sq_le_normSq_sub_of_imaginary_reverse
    {gap : Fraction.Rational} (gapNonnegative : 0 ≤ gap)
    {left right : Basic.Canonical} (lower : gap ≤ right.im - left.im) :
    gap ^ 2 ≤ Basic.normSq (left - right) := by
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (right.im - left.im) ^ 2 := squares
    _ = 0 + (left.im - right.im) ^ 2 := by ring1
    _ ≤ Basic.normSq (left - right) :=
      add_le_add
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (left.re - right.re))
        (le_refl _)

end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonnegative gap below the forward real displacement has square at most the full Gaussian squared distance. -/
public theorem sq_le_normSq_sub_of_real_forward
    {gap : Fraction.Rational} (gapNonnegative : 0 ≤ gap)
    {left right : Basic.Canonical} (lower : gap ≤ left.re - right.re) :
    gap ^ 2 ≤ Basic.normSq (left - right) := by
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (left.re - right.re) ^ 2 := squares
    _ = (left.re - right.re) ^ 2 + 0 := by ring1
    _ ≤ Basic.normSq (left - right) :=
      add_le_add (le_refl _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (left.im - right.im))

end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonnegative gap below the reverse real displacement has square at most the full Gaussian squared distance. -/
public theorem sq_le_normSq_sub_of_real_reverse
    {gap : Fraction.Rational} (gapNonnegative : 0 ≤ gap)
    {left right : Basic.Canonical} (lower : gap ≤ right.re - left.re) :
    gap ^ 2 ≤ Basic.normSq (left - right) := by
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    gapNonnegative lower 2
  calc
    gap ^ 2 ≤ (right.re - left.re) ^ 2 := squares
    _ = (left.re - right.re) ^ 2 + 0 := by ring1
    _ ≤ Basic.normSq (left - right) :=
      add_le_add (le_refl _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (left.im - right.im))

end Purelib.Data.Gaussian.Norm.Bounds

end

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data Purelib.Algebra

/-- The square of a rational difference is bounded by twice the input squares.

Apply the sum-square bound to the retained negated second input; its square
equals the original square by the direct product-negation identity. -/
private theorem Norm.Bounds.sub_sq_le_two_squares (left right : Fraction.Rational) :
    (left - right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  rw [Rat.Fraction.Arithmetic.sub_eq_add_neg_direct]
  calc
    (left + -right) ^ 2 ≤ 2 * (left ^ 2 + (-right) ^ 2) :=
      Purelib.Data.Rat.Bounds.Square.add_sq_le_two left (-right)
    _ = 2 * (left ^ 2 + right ^ 2) := by
      have negativeSquare : (-right) ^ 2 = right ^ 2 := by
        rw [pow_two, pow_two, Ring.Multiplication.neg_mul_neg]
      rw [negativeSquare]
end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

/-- The quadrance of a Gaussian difference is bounded by twice the input quadrances.

The two original coordinate differences retain their rational square bounds;
summing those bounds retains both input quadrances. -/
theorem Norm.Bounds.normSq_sub_le_two (left right : Basic.Canonical) :
    Norm.Basic.normSq (left - right) ≤
      2 * (Norm.Basic.normSq left + Norm.Basic.normSq right) := by
  change (left.re - right.re) ^ 2 + (left.im - right.im) ^ 2 ≤
    2 * ((left.re ^ 2 + left.im ^ 2) + (right.re ^ 2 + right.im ^ 2))
  calc
    (left.re - right.re) ^ 2 + (left.im - right.im) ^ 2 ≤
        2 * (left.re ^ 2 + right.re ^ 2) + 2 * (left.im ^ 2 + right.im ^ 2) :=
      Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (Norm.Bounds.sub_sq_le_two_squares left.re right.re)
        (Norm.Bounds.sub_sq_le_two_squares left.im right.im)
    _ = 2 * ((left.re ^ 2 + left.im ^ 2) + (right.re ^ 2 + right.im ^ 2)) := by ring1

end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data Purelib.Algebra

/-- Twice a rational product with its sum equals the corresponding square expression.

Both displayed inputs are retained in the difference of their squares and
the square of their sum; the identity holds for either sign. -/
private theorem Norm.Bounds.twice_self_mul_sum (left right : Fraction.Rational) :
    2 * (left * (left + right)) =
      left ^ 2 - right ^ 2 + (left + right) ^ 2 := by
  ring1
end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data Purelib.Algebra

/-- A positive quadrance gap gives a lower bound for the quadrance of the sum.

The positive margin is bounded by the original difference of input quadrances.
The denominator uses four times the first input quadrance, which this gap
proves positive. -/
theorem Norm.Bounds.normSq_add_lower_of_gap
    {left right : Gaussian.Basic.Canonical} {margin : Rat.Fraction.Rational}
    (marginPositive : 0 < margin)
    (gap : margin ≤ Norm.Basic.normSq left - Norm.Basic.normSq right) :
    margin ^ 2 / (4 * Norm.Basic.normSq left) ≤ Norm.Basic.normSq (left + right) :=
      by
  let sum := left + right
  let product := Basic.conj left * sum
  let dot := product.re
  have leftNormPositive : 0 < Norm.Basic.normSq left := by
    have gapLeNorm : margin ≤ Norm.Basic.normSq left :=
      gap.trans (by
        have bound := Rat.Fraction.Order.Arithmetic.neg_le_neg_direct
          (Gaussian.Norm.Basic.normSq_nonneg right)
        rw [neg_zero] at bound
        change Norm.Basic.normSq left + -Norm.Basic.normSq right ≤ _
        have translated := Rat.Fraction.Order.Arithmetic.add_le_add_direct
          (le_refl (Norm.Basic.normSq left)) bound
        rw [add_zero] at translated
        exact translated)
    exact marginPositive.trans_le gapLeNorm
  have fourPositive : (0 : Rat.Fraction.Rational) < 4 :=
    Rat.Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide)
  have denominatorPositive : 0 < 4 * Norm.Basic.normSq left :=
    Rat.Fraction.Order.Arithmetic.mul_pos_direct fourPositive leftNormPositive
  have sumNormNonnegative : 0 ≤ Norm.Basic.normSq sum := Gaussian.Norm.Basic.normSq_nonneg sum
  have doubledDot : 2 * dot =
      (Norm.Basic.normSq left - Norm.Basic.normSq right) +
        Norm.Basic.normSq sum := by
    have productReal : dot = left.re * sum.re + left.im * sum.im := by
      change left.re * sum.re - (-left.im) * sum.im = _
      ring1
    rw [productReal]
    change 2 * (left.re * (left.re + right.re) + left.im * (left.im + right.im)) =
      ((left.re ^ 2 + left.im ^ 2) - (right.re ^ 2 + right.im ^ 2)) +
        ((left.re + right.re) ^ 2 + (left.im + right.im) ^ 2)
    rw [mul_add, Norm.Bounds.twice_self_mul_sum left.re right.re,
      Norm.Bounds.twice_self_mul_sum left.im right.im]
    ring1
  have marginLeDoubledDot : margin ≤ 2 * dot := by
    rw [doubledDot]
    exact gap.trans (le_add_of_nonneg_right sumNormNonnegative)
  have squaredMargin : margin ^ 2 ≤ (2 * dot) ^ 2 :=
    Rat.Fraction.Order.Arithmetic.pow_le_pow_direct marginPositive.le
      marginLeDoubledDot 2
  have dotCauchy : dot ^ 2 ≤ Norm.Basic.normSq left * Norm.Basic.normSq sum := by
    calc
      dot ^ 2 ≤ dot ^ 2 + product.im ^ 2 :=
        le_add_of_nonneg_right
          (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct product.im)
      _ = Norm.Basic.normSq product := by rfl
      _ = Norm.Basic.normSq (Basic.conj left) * Norm.Basic.normSq
        sum := Gaussian.Norm.Basic.normSq_mul _ _
      _ = Norm.Basic.normSq left * Norm.Basic.normSq sum := by
        rw [Gaussian.Norm.Basic.normSq_conj]
  apply (Rat.Fraction.Order.Field.div_le_iff_pos
    denominatorPositive).2
  rw [_root_.mul_comm (Norm.Basic.normSq sum)]
  calc
    margin ^ 2 ≤ (2 * dot) ^ 2 := squaredMargin
    _ = 4 * dot ^ 2 := by
      rw [pow_two, pow_two]
      ring1
    _ ≤ 4 * (Norm.Basic.normSq left * Norm.Basic.normSq sum) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        dotCauchy fourPositive.le
    _ = (4 * Norm.Basic.normSq left) * Norm.Basic.normSq sum :=
      (_root_.mul_assoc _ _ _).symm
end Gaussian

end Purelib.Data

end

end

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section
@[expose] public section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

namespace Purelib.Data.Gaussian

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The difference of squared norms, squared, is bounded by twice the squared distance times the sum of endpoint squared
norms. -/
public theorem normSq_difference_sq_le_two_mul
    (left right : Basic.Canonical) :
    (Norm.Basic.normSq left - Norm.Basic.normSq right) ^ 2 ≤
      2 * Norm.Basic.normSq (left - right) * (Norm.Basic.normSq left + Norm.Basic.normSq
        right) := by
  let difference := left - right
  let total := left + right
  let dot := difference.re * total.re + difference.im * total.im
  have dotIdentity : dot = Norm.Basic.normSq left - Norm.Basic.normSq right := by
    dsimp only [dot, difference, total, Norm.Basic.normSq]
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im]
    ring1
  have cauchy : dot ^ 2 ≤ Norm.Basic.normSq difference * Norm.Basic.normSq total := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (difference.re * total.im - difference.im * total.re) ^ 2 :=
        Fraction.Order.Arithmetic.sq_nonneg_direct _
      _ = Norm.Basic.normSq difference * Norm.Basic.normSq total - dot ^ 2 := by
        dsimp only [Norm.Basic.normSq, dot]
        ring1
  calc
    (Norm.Basic.normSq left - Norm.Basic.normSq right) ^ 2 = dot ^ 2 := by rw [dotIdentity]
    _ ≤ Norm.Basic.normSq difference * Norm.Basic.normSq total := cauchy
    _ ≤ Norm.Basic.normSq difference *
        (2 * (Norm.Basic.normSq left + Norm.Basic.normSq right)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Norm.Bounds.normSq_add_le_two left right) (Norm.Basic.normSq_nonneg difference)
    _ = 2 * Norm.Basic.normSq (left - right) *
        (Norm.Basic.normSq left + Norm.Basic.normSq right) := by
      dsimp only [difference]
      ring1

end Purelib.Data.Gaussian

end

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Basic
namespace BoundaryClearance

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A strict quarter-target bound and a weak quarter-target bound give a strict target bound on the sum norm. -/
theorem normSq_add_lt_of_quarters
    {left right : Basic.Canonical} {target : Fraction.Rational}
    (leftSmall : Data.Gaussian.Norm.Basic.normSq left < target / 4)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq right ≤ target / 4) :
    Data.Gaussian.Norm.Basic.normSq (left + right) < target := by
  have valueUpper := Norm.Bounds.normSq_add_le_two left right
  have sumStrict : Data.Gaussian.Norm.Basic.normSq left + Data.Gaussian.Norm.Basic.normSq right < target / 2 := by
    have first := Fraction.Order.Arithmetic.add_lt_add_right_direct leftSmall
      (Data.Gaussian.Norm.Basic.normSq right)
    have second : target / 4 + Data.Gaussian.Norm.Basic.normSq right ≤
        target / 4 + target / 4 := by
      calc
        target / 4 + Data.Gaussian.Norm.Basic.normSq right = Data.Gaussian.Norm.Basic.normSq right + target / 4 :=
          _root_.add_comm _ _
        _ ≤ target / 4 + target / 4 :=
          Fraction.Order.Arithmetic.add_le_add_right_direct rightSmall
            (target / 4)
    exact (first.trans_le second).trans_eq (by
      apply Fraction.Field.mul_right_cancel_of_ne
        (show (4 : Fraction.Rational) ≠ 0 by decide)
      calc
        (target / 4 + target / 4) * 4 =
            (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
        _ = target + target := by
          rw [show target / 4 * 4 = target from
            Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
        _ = target * 2 := by ring1
        _ = ((target / 2) * 2) * 2 := by
          rw [show target / 2 * 2 = target from
            Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
        _ = (target / 2) * (2 * 2) :=
          Fraction.Field.mul_assoc (target / 2) 2 2
        _ = (target / 2) * 4 := by
          rw [show (2 : Fraction.Rational) * 2 = 4 by decide])
  have twiceStrict : 2 * (Data.Gaussian.Norm.Basic.normSq left + Data.Gaussian.Norm.Basic.normSq right) < target := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 2 by decide) sumStrict
    calc
      2 * (Data.Gaussian.Norm.Basic.normSq left + Data.Gaussian.Norm.Basic.normSq right) < 2 * (target / 2) := scaled
      _ = target := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)
  exact valueUpper.trans_lt twiceStrict
end BoundaryClearance

end Purelib.Polynomial.Clearance.Box.Boundary.Basic

end

/-!
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Riemann.Integration.LegendreGaussManin

end Purelib.Riemann.Integration.LegendreGaussManin

end

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Riemann.Integration.LegendreGaussManin

end Purelib.Riemann.Integration.LegendreGaussManin

end

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Riemann.Periods.Bilinear

end Purelib.Riemann.Periods.Bilinear

end

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
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
# Finite reciprocal clearance at the existing outer radius

The coefficient radius used by the original winding square also controls
the reversed polynomial on the reciprocal disk. The explicit quarter-sized
tail bound supplies a positive uniform radicand margin, including the chart
origin. A separate coordinate factor accounts for an odd-degree branch.
No ambient enlargement or limiting argument is used.
-/

section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Riemann.Periods.Bilinear

end Purelib.Riemann.Periods.Bilinear

end

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
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

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A displacement bound from a center bounds the value norm by twice the sum of center norm and displacement bound. -/
theorem value_normSq_le_of_offset {value center : Basic.Canonical} {bound :
  Fraction.Rational}
    (offsetBound : Data.Gaussian.Norm.Basic.normSq (value - center) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq value ≤ 2 * (Data.Gaussian.Norm.Basic.normSq center + bound) := by
  have sumBound := normSq_add_le_two (value - center) center
  have identity : value - center + center = value := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;>
      ring1
  rw [identity] at sumBound
  apply sumBound.trans
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
    (show (0 : Fraction.Rational) ≤ 2 by decide)
  calc
    Data.Gaussian.Norm.Basic.normSq (value - center) + Data.Gaussian.Norm.Basic.normSq center ≤
        bound + Data.Gaussian.Norm.Basic.normSq center :=
      add_le_add offsetBound (le_refl _)
    _ = Data.Gaussian.Norm.Basic.normSq center + bound := by ring1
end Purelib.Data.Gaussian.Norm.Bounds

end

public section
namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- A square residual below the parameter norm forces its coordinate to be nonzero.

The residual is strictly below a bound which does not exceed the parameter's
squared norm. A zero coordinate would give that same norm as the residual,
contradicting the strict comparison. -/
theorem coordinate_nonzero {coordinate parameter : Basic.Canonical} {bound : Fraction.Rational}
    (accurate : Basic.normSq (coordinate * coordinate - parameter) < bound)
    (small : bound ≤ Basic.normSq parameter) : coordinate ≠ 0 := by
  intro zero
  rw [zero, Basic.mul_zero, Basic.zero_sub, Norm.Basic.normSq_neg] at accurate
  exact (lt_irrefl _ (accurate.trans_le small))

end Purelib.Data.Gaussian.Norm.Bounds

public section

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data
open Purelib.Data.Rat

/-- The elementary lune inclusion behind the diagonal case of Lakein's
first inequality.  A point in the open unit disc about `(1,1)` but outside
the unit disc about zero cannot be moved into the latter disc by a vector in
the closed half-square whose translated corner is exterior to the two
adjacent unit discs.

The four retained rational coordinates and three disc comparisons determine the translated northeast corner. The strict
open-disc bound and the exact two closed half-square lower bounds are preserved in the resulting weak corner bound. -/
public theorem northeast_lune_exterior
    (rhoReal rhoImaginary yReal yImaginary : Fraction.Rational)
    (rhoRealLower : -(1 / 2 : Fraction.Rational) ≤ rhoReal)
    (rhoImaginaryLower : -(1 / 2 : Fraction.Rational) ≤ rhoImaginary)
    (yInside : yReal ^ 2 + yImaginary ^ 2 < 1)
    (realExterior :
      1 ≤ (1 + rhoReal) ^ 2 + rhoImaginary ^ 2)
    (imaginaryExterior :
      1 ≤ rhoReal ^ 2 + (1 + rhoImaginary) ^ 2)
    (translatedInside :
      (1 + rhoReal + yReal) ^ 2 +
          (1 + rhoImaginary + yImaginary) ^ 2 ≤ 1) :
    (1 + yReal) ^ 2 + (1 + yImaginary) ^ 2 ≤ 1 := by
  let rhoNorm := rhoReal ^ 2 + rhoImaginary ^ 2
  let realCoordinate := 1 + yReal
  let imaginaryCoordinate := 1 + yImaginary
  have yRealSquareLt : yReal ^ 2 < 1 := by
    exact ((fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
      (show a ≤ a + b from by
        simpa only [add_zero, -eq_self, -iff_self] using
          Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_refl a) h))
      (Fraction.Order.Arithmetic.sq_nonneg_direct yImaginary)).trans_lt
        yInside
  have yImaginarySquareLt : yImaginary ^ 2 < 1 := by
    have reordered : yImaginary ^ 2 + yReal ^ 2 < 1 := by
      calc
        yImaginary ^ 2 + yReal ^ 2 =
            yReal ^ 2 + yImaginary ^ 2 := by ring1
        _ < 1 := yInside
    exact ((fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
      (show a ≤ a + b from by
        simpa only [add_zero, -eq_self, -iff_self] using
          Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_refl a) h))
      (Fraction.Order.Arithmetic.sq_nonneg_direct yReal)).trans_lt
        reordered
  have realCoordinatePositive : 0 < realCoordinate := by
    have lower := Fraction.Order.Square.neg_one_lt_of_square_lt_one yRealSquareLt
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct lower 1
    calc
      0 = (-1 : Fraction.Rational) + 1 := by ring1
      _ < yReal + 1 := shifted
      _ = realCoordinate := by dsimp only [realCoordinate]; ring1
  have imaginaryCoordinatePositive : 0 < imaginaryCoordinate := by
    have lower := Fraction.Order.Square.neg_one_lt_of_square_lt_one yImaginarySquareLt
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct lower 1
    calc
      0 = (-1 : Fraction.Rational) + 1 := by ring1
      _ < yImaginary + 1 := shifted
      _ = imaginaryCoordinate := by dsimp only [imaginaryCoordinate]; ring1
  have realExteriorGap : 0 ≤ rhoNorm + 2 * rhoReal := by
    have gap := Fraction.Order.Arithmetic.sub_nonneg_direct realExterior
    calc
      0 ≤ ((1 + rhoReal) ^ 2 + rhoImaginary ^ 2) - 1 := gap
      _ = rhoNorm + 2 * rhoReal := by
        dsimp only [rhoNorm]
        ring1
  have imaginaryExteriorGap : 0 ≤ rhoNorm + 2 * rhoImaginary := by
    have gap := Fraction.Order.Arithmetic.sub_nonneg_direct imaginaryExterior
    calc
      0 ≤ (rhoReal ^ 2 + (1 + rhoImaginary) ^ 2) - 1 := gap
      _ = rhoNorm + 2 * rhoImaginary := by
        dsimp only [rhoNorm]
        ring1
  have notBothNegative : ¬ (rhoReal < 0 ∧ rhoImaginary < 0) := by
    rintro ⟨rhoRealNegative, rhoImaginaryNegative⟩
    have negRealNonnegative : 0 ≤ -rhoReal :=
      (by have translated := Fraction.Order.Arithmetic.neg_le_neg_direct rhoRealNegative.le; simpa only [show -(0 :
        Fraction.Rational) = 0 by decide] using translated)
    have negImaginaryNonnegative : 0 ≤ -rhoImaginary :=
      (by have translated := Fraction.Order.Arithmetic.neg_le_neg_direct rhoImaginaryNegative.le; simpa only [show -(0 :
        Fraction.Rational) = 0 by decide] using translated)
    have negRealLeHalf : -rhoReal ≤ (1 / 2 : Fraction.Rational) := by
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct rhoRealLower
      simpa only [neg_neg] using reversed
    have negImaginaryLeHalf :
        -rhoImaginary ≤ (1 / 2 : Fraction.Rational) := by
      have reversed :=
        Fraction.Order.Arithmetic.neg_le_neg_direct rhoImaginaryLower
      simpa only [neg_neg] using reversed
    have realSquareBound : 2 * rhoReal ^ 2 ≤ -rhoReal := by
      have factorNonnegative : 0 ≤ 2 * (-rhoReal) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          (show (0 : Fraction.Rational) ≤ 2 by decide) negRealNonnegative
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          negRealLeHalf factorNonnegative
      calc
        2 * rhoReal ^ 2 = (-rhoReal) * (2 * (-rhoReal)) := by ring1
        _ ≤ (1 / 2 : Fraction.Rational) * (2 * (-rhoReal)) := scaled
        _ = -rhoReal := by
          calc
            (1 / 2 : Fraction.Rational) * (2 * (-rhoReal)) =
                ((1 / 2 : Fraction.Rational) * 2) * (-rhoReal) := by
              exact (_root_.mul_assoc (1 / 2 : Fraction.Rational) 2 (-rhoReal)).symm
            _ = 1 * (-rhoReal) := by
              rw [show (1 / 2 : Fraction.Rational) * 2 = 1 by decide]
            _ = -rhoReal := one_mul _
    have imaginarySquareBound :
        2 * rhoImaginary ^ 2 ≤ -rhoImaginary := by
      have factorNonnegative : 0 ≤ 2 * (-rhoImaginary) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          (show (0 : Fraction.Rational) ≤ 2 by decide) negImaginaryNonnegative
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          negImaginaryLeHalf factorNonnegative
      calc
        2 * rhoImaginary ^ 2 =
            (-rhoImaginary) * (2 * (-rhoImaginary)) := by ring1
        _ ≤ (1 / 2 : Fraction.Rational) * (2 * (-rhoImaginary)) := scaled
        _ = -rhoImaginary := by
          calc
            (1 / 2 : Fraction.Rational) * (2 * (-rhoImaginary)) =
                ((1 / 2 : Fraction.Rational) * 2) * (-rhoImaginary) := by
              exact (_root_.mul_assoc
                (1 / 2 : Fraction.Rational) 2 (-rhoImaginary)).symm
            _ = 1 * (-rhoImaginary) := by
              rw [show (1 / 2 : Fraction.Rational) * 2 = 1 by decide]
            _ = -rhoImaginary := one_mul _
    have twiceRhoNormUpper :
        2 * rhoNorm ≤ -(rhoReal + rhoImaginary) := by
      calc
        2 * rhoNorm = 2 * rhoReal ^ 2 +
            2 * rhoImaginary ^ 2 := by
          dsimp only [rhoNorm]
          ring1
        _ ≤ -rhoReal + -rhoImaginary :=
          Fraction.Order.Arithmetic.add_le_add_direct
            realSquareBound imaginarySquareBound
        _ = -(rhoReal + rhoImaginary) := by ring1
    have summedGap :
        0 ≤ (rhoNorm + 2 * rhoReal) +
          (rhoNorm + 2 * rhoImaginary) :=
      add_nonneg realExteriorGap imaginaryExteriorGap
    have sumNegative : rhoReal + rhoImaginary < 0 :=
      Fraction.Order.Arithmetic.add_lt_add_direct
        rhoRealNegative rhoImaginaryNegative
    have impossible :
        (rhoNorm + 2 * rhoReal) +
            (rhoNorm + 2 * rhoImaginary) < 0 := by
      calc
        (rhoNorm + 2 * rhoReal) +
              (rhoNorm + 2 * rhoImaginary) =
            2 * rhoNorm + 2 * (rhoReal + rhoImaginary) := by ring1
        _ ≤ -(rhoReal + rhoImaginary) +
            2 * (rhoReal + rhoImaginary) :=
          Fraction.Order.Arithmetic.add_le_add_right_direct
            twiceRhoNormUpper (2 * (rhoReal + rhoImaginary))
        _ = rhoReal + rhoImaginary := by ring1
        _ < 0 := sumNegative
    exact (not_lt_of_ge summedGap impossible)
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro outside
  have translatedStrict :
      (1 + rhoReal + yReal) ^ 2 +
          (1 + rhoImaginary + yImaginary) ^ 2 <
        (1 + yReal) ^ 2 + (1 + yImaginary) ^ 2 :=
    translatedInside.trans_lt outside
  have differenceNegative :
      rhoNorm + 2 * realCoordinate * rhoReal +
          2 * imaginaryCoordinate * rhoImaginary < 0 := by
    have difference :=
      Fraction.Order.Arithmetic.sub_neg_direct translatedStrict
    calc
      rhoNorm + 2 * realCoordinate * rhoReal +
            2 * imaginaryCoordinate * rhoImaginary =
          ((1 + rhoReal + yReal) ^ 2 +
              (1 + rhoImaginary + yImaginary) ^ 2) -
            ((1 + yReal) ^ 2 + (1 + yImaginary) ^ 2) := by
        dsimp only [rhoNorm, realCoordinate, imaginaryCoordinate]
        ring1
      _ < 0 := difference
  by_cases realNonnegative : 0 ≤ rhoReal
  · by_cases imaginaryNonnegative : 0 ≤ rhoImaginary
    · have realTerm :
          0 ≤ 2 * realCoordinate * rhoReal := by
        exact Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (show (0 : Fraction.Rational) ≤ 2 by decide)
            realCoordinatePositive.le) realNonnegative
      have imaginaryTerm :
          0 ≤ 2 * imaginaryCoordinate * rhoImaginary := by
        exact Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (show (0 : Fraction.Rational) ≤ 2 by decide)
            imaginaryCoordinatePositive.le) imaginaryNonnegative
      have nonnegative := add_nonneg
        (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct rhoReal)
          (Fraction.Order.Arithmetic.sq_nonneg_direct rhoImaginary))
        (add_nonneg realTerm imaginaryTerm)
      have reordered :
          0 ≤ rhoNorm + 2 * realCoordinate * rhoReal +
            2 * imaginaryCoordinate * rhoImaginary := by
        calc
          0 ≤ (rhoReal ^ 2 + rhoImaginary ^ 2) +
              (2 * realCoordinate * rhoReal +
                2 * imaginaryCoordinate * rhoImaginary) := nonnegative
          _ = rhoNorm + 2 * realCoordinate * rhoReal +
              2 * imaginaryCoordinate * rhoImaginary := by
            dsimp only [rhoNorm]
            ring1
      exact (not_lt_of_ge reordered differenceNegative)
    · have imaginaryNegative : rhoImaginary < 0 :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct imaginaryNonnegative
      by_cases coordinateLeOne : imaginaryCoordinate ≤ 1
      · have productComparison :
            rhoImaginary ≤ imaginaryCoordinate * rhoImaginary := by
          have coordinateGap : 0 ≤ 1 - imaginaryCoordinate :=
            Fraction.Order.Arithmetic.sub_nonneg_direct coordinateLeOne
          have productNonnegative :=
            Fraction.Order.Arithmetic.mul_nonneg_direct
              (by have translated := Fraction.Order.Arithmetic.neg_le_neg_direct imaginaryNegative.le; simpa only [show
                -(0 : Fraction.Rational) = 0 by decide] using translated) coordinateGap
          calc
            rhoImaginary ≤ rhoImaginary +
                ((-rhoImaginary) * (1 - imaginaryCoordinate)) :=
              (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
                (show a ≤ a + b from by
                  simpa only [add_zero, -eq_self, -iff_self] using
                    Fraction.Order.Arithmetic.add_le_add_direct
                      (Fraction.Order.Basic.le_refl a) h)) productNonnegative
            _ = imaginaryCoordinate * rhoImaginary := by ring1
        have scaledComparison :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            productComparison (show (0 : Fraction.Rational) ≤ 2 by decide)
        have imaginaryPart :
            0 ≤ rhoNorm + 2 * imaginaryCoordinate * rhoImaginary := by
          calc
            0 ≤ rhoNorm + 2 * rhoImaginary := imaginaryExteriorGap
            _ ≤ rhoNorm + 2 * imaginaryCoordinate * rhoImaginary :=
              calc
                rhoNorm + 2 * rhoImaginary =
                    2 * rhoImaginary + rhoNorm := by ring1
                _ ≤ 2 * (imaginaryCoordinate * rhoImaginary) + rhoNorm :=
                  Fraction.Order.Arithmetic.add_le_add_direct
                    scaledComparison le_rfl
                _ = rhoNorm + 2 * imaginaryCoordinate * rhoImaginary := by
                  ring1
        have realPart :
            0 ≤ 2 * realCoordinate * rhoReal :=
          Fraction.Order.Arithmetic.mul_nonneg_direct
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (show (0 : Fraction.Rational) ≤ 2 by decide)
              realCoordinatePositive.le) realNonnegative
        have reordered := add_nonneg imaginaryPart realPart
        have final :
            0 ≤ rhoNorm + 2 * realCoordinate * rhoReal +
              2 * imaginaryCoordinate * rhoImaginary := by
          calc
            0 ≤ (rhoNorm + 2 * imaginaryCoordinate * rhoImaginary) +
                2 * realCoordinate * rhoReal := reordered
            _ = rhoNorm + 2 * realCoordinate * rhoReal +
                2 * imaginaryCoordinate * rhoImaginary := by ring1
        exact (not_lt_of_ge final differenceNegative)
      · have coordinateGreater : 1 < imaginaryCoordinate :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct coordinateLeOne
        have yImaginaryPositive : 0 < yImaginary := by
          have shifted :=
            Fraction.Order.Arithmetic.sub_lt_sub_right_direct
              coordinateGreater 1
          calc
            0 = (1 : Fraction.Rational) - 1 := by ring1
            _ < imaginaryCoordinate - 1 := shifted
            _ = yImaginary := by
              dsimp only [imaginaryCoordinate]
              ring1
        have baseImaginaryNonnegative : 0 ≤ 1 + rhoImaginary := by
          calc
            0 ≤ 1 + (-(1 / 2 : Fraction.Rational)) := by decide
            _ ≤ 1 + rhoImaginary := by
              calc
                1 + (-(1 / 2 : Fraction.Rational)) =
                    (-(1 / 2 : Fraction.Rational)) + 1 := by ring1
                _ ≤ rhoImaginary + 1 :=
                  Fraction.Order.Arithmetic.add_le_add_direct
                    rhoImaginaryLower le_rfl
                _ = 1 + rhoImaginary := by ring1
        have baseRealSquareLe : rhoReal ^ 2 ≤
            (rhoReal + realCoordinate) ^ 2 := by
          have strict : rhoReal < rhoReal + realCoordinate := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
              realCoordinatePositive rhoReal
            calc
              rhoReal = rhoReal + 0 := by ring1
              _ < rhoReal + realCoordinate := shifted
          exact (Fraction.Order.Square.square_lt_square_of_nonneg_of_lt realNonnegative strict).le
        have baseImaginaryStrict :
            1 + rhoImaginary < 1 + rhoImaginary + yImaginary := by
          have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
            yImaginaryPositive (1 + rhoImaginary)
          calc
            1 + rhoImaginary = 1 + rhoImaginary + 0 := by ring1
            _ < 1 + rhoImaginary + yImaginary := shifted
        have baseImaginarySquareStrict :=
          Fraction.Order.Square.square_lt_square_of_nonneg_of_lt baseImaginaryNonnegative
            baseImaginaryStrict
        have exteriorStrict :
            1 < (rhoReal + realCoordinate) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 := by
          calc
            1 ≤ rhoReal ^ 2 + (1 + rhoImaginary) ^ 2 :=
              imaginaryExterior
            _ < (rhoReal + realCoordinate) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 :=
              calc
                rhoReal ^ 2 + (1 + rhoImaginary) ^ 2 ≤
                    (rhoReal + realCoordinate) ^ 2 +
                      (1 + rhoImaginary) ^ 2 :=
                  Fraction.Order.Arithmetic.add_le_add_direct
                    baseRealSquareLe le_rfl
                _ < (rhoReal + realCoordinate) ^ 2 +
                    (1 + rhoImaginary + yImaginary) ^ 2 :=
                  Fraction.Order.Arithmetic.add_lt_add_left_direct
                    baseImaginarySquareStrict
                    ((rhoReal + realCoordinate) ^ 2)
        have translatedIdentity :
            (rhoReal + realCoordinate) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 =
              (1 + rhoReal + yReal) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 := by
          dsimp only [realCoordinate]
          ring1
        rw [translatedIdentity] at exteriorStrict
        exact (not_lt_of_ge translatedInside exteriorStrict)
  · have realNegative : rhoReal < 0 :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct realNonnegative
    have imaginaryNonnegative : 0 ≤ rhoImaginary := by
      apply Fraction.Order.Arithmetic.le_of_not_gt_direct
      intro imaginaryNegative
      exact notBothNegative ⟨realNegative, imaginaryNegative⟩
    by_cases coordinateLeOne : realCoordinate ≤ 1
    · have productComparison :
          rhoReal ≤ realCoordinate * rhoReal := by
        have coordinateGap : 0 ≤ 1 - realCoordinate :=
          Fraction.Order.Arithmetic.sub_nonneg_direct coordinateLeOne
        have productNonnegative :=
          Fraction.Order.Arithmetic.mul_nonneg_direct
            (by have translated := Fraction.Order.Arithmetic.neg_le_neg_direct realNegative.le; simpa only [show -(0 :
              Fraction.Rational) = 0 by decide] using translated) coordinateGap
        calc
          rhoReal ≤ rhoReal + ((-rhoReal) * (1 - realCoordinate)) :=
            (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) productNonnegative
          _ = realCoordinate * rhoReal := by ring1
      have scaledComparison :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          productComparison (show (0 : Fraction.Rational) ≤ 2 by decide)
      have realPart :
          0 ≤ rhoNorm + 2 * realCoordinate * rhoReal := by
        calc
          0 ≤ rhoNorm + 2 * rhoReal := realExteriorGap
          _ ≤ rhoNorm + 2 * realCoordinate * rhoReal :=
            calc
              rhoNorm + 2 * rhoReal = 2 * rhoReal + rhoNorm := by ring1
              _ ≤ 2 * (realCoordinate * rhoReal) + rhoNorm :=
                Fraction.Order.Arithmetic.add_le_add_direct
                  scaledComparison le_rfl
              _ = rhoNorm + 2 * realCoordinate * rhoReal := by ring1
      have imaginaryPart :
          0 ≤ 2 * imaginaryCoordinate * rhoImaginary :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (show (0 : Fraction.Rational) ≤ 2 by decide)
            imaginaryCoordinatePositive.le) imaginaryNonnegative
      have final := add_nonneg realPart imaginaryPart
      exact (not_lt_of_ge final differenceNegative)
    · have coordinateGreater : 1 < realCoordinate :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct coordinateLeOne
      have yRealPositive : 0 < yReal := by
        have shifted :=
          Fraction.Order.Arithmetic.sub_lt_sub_right_direct
            coordinateGreater 1
        calc
          0 = (1 : Fraction.Rational) - 1 := by ring1
          _ < realCoordinate - 1 := shifted
          _ = yReal := by
            dsimp only [realCoordinate]
            ring1
      have baseRealNonnegative : 0 ≤ 1 + rhoReal := by
        calc
          0 ≤ 1 + (-(1 / 2 : Fraction.Rational)) := by decide
          _ ≤ 1 + rhoReal := by
            calc
              1 + (-(1 / 2 : Fraction.Rational)) =
                  (-(1 / 2 : Fraction.Rational)) + 1 := by ring1
              _ ≤ rhoReal + 1 :=
                Fraction.Order.Arithmetic.add_le_add_direct
                  rhoRealLower le_rfl
              _ = 1 + rhoReal := by ring1
      have baseRealStrict :
          1 + rhoReal < 1 + rhoReal + yReal := by
        have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
          yRealPositive (1 + rhoReal)
        calc
          1 + rhoReal = 1 + rhoReal + 0 := by ring1
          _ < 1 + rhoReal + yReal := shifted
      have baseRealSquareStrict :=
        Fraction.Order.Square.square_lt_square_of_nonneg_of_lt baseRealNonnegative baseRealStrict
      have baseImaginarySquareLe : rhoImaginary ^ 2 ≤
          (rhoImaginary + imaginaryCoordinate) ^ 2 := by
        have strict :
            rhoImaginary < rhoImaginary + imaginaryCoordinate := by
          have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
            imaginaryCoordinatePositive rhoImaginary
          calc
            rhoImaginary = rhoImaginary + 0 := by ring1
            _ < rhoImaginary + imaginaryCoordinate := shifted
        exact (Fraction.Order.Square.square_lt_square_of_nonneg_of_lt imaginaryNonnegative strict).le
      have exteriorStrict :
          1 < (1 + rhoReal + yReal) ^ 2 +
              (rhoImaginary + imaginaryCoordinate) ^ 2 := by
        calc
          1 ≤ (1 + rhoReal) ^ 2 + rhoImaginary ^ 2 := realExterior
          _ < (1 + rhoReal + yReal) ^ 2 +
              (rhoImaginary + imaginaryCoordinate) ^ 2 :=
            calc
              (1 + rhoReal) ^ 2 + rhoImaginary ^ 2 <
                  (1 + rhoReal + yReal) ^ 2 + rhoImaginary ^ 2 :=
                Fraction.Order.Arithmetic.add_lt_add_right_direct
                  baseRealSquareStrict (rhoImaginary ^ 2)
              _ ≤ (1 + rhoReal + yReal) ^ 2 +
                  (rhoImaginary + imaginaryCoordinate) ^ 2 :=
                Fraction.Order.Arithmetic.add_le_add_direct
                  le_rfl baseImaginarySquareLe
      have translatedIdentity :
          (1 + rhoReal + yReal) ^ 2 +
              (rhoImaginary + imaginaryCoordinate) ^ 2 =
            (1 + rhoReal + yReal) ^ 2 +
              (1 + rhoImaginary + yImaginary) ^ 2 := by
        dsimp only [imaginaryCoordinate]
        ring1
      rw [translatedIdentity] at exteriorStrict
      exact (not_lt_of_ge translatedInside exteriorStrict)

end Purelib.Data.Gaussian.Norm.Bounds

public section
namespace Purelib.Data.Gaussian.Norm.Bounds

/-- Two successive original squared-norm discrepancies below quarter targets pay their full combined target. -/
public theorem normSq_sub_lt_of_quarter_bounds {first middle last : Purelib.Data.Gaussian.Basic.Canonical} {target :
  Purelib.Data.Rat.Fraction.Rational}
    (left : Basic.normSq (first - middle) < target / 4) (right :
      Basic.normSq (middle - last) < target / 4) :
    Basic.normSq (first - last) < target := by
  rw [show first - last = (first - middle) + (middle - last) by ring1]
  apply (normSq_add_le_two _ _).trans_lt
  apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : Purelib.Data.Rat.Fraction.Rational) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct left right)).trans_eq
  rw [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end Purelib.Data.Gaussian.Norm.Bounds

end

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Three successive displacement bounds give the retained nested twice-sum bound on the endpoint squared distance. -/
public theorem normSq_sub_le_weighted_sum
    (first second third fourth : Basic.Canonical)
    (firstBound middleBound lastBound :
      Fraction.Rational)
    (firstClose :
      Basic.normSq (first - second) <=
        firstBound)
    (middleClose :
      Basic.normSq (second - third) <=
        middleBound)
    (lastClose :
      Basic.normSq (third - fourth) <=
        lastBound) :
    Basic.normSq (first - fourth) <=
      2 * (firstBound + 2 * (middleBound + lastBound)) := by
  have throughThird :=
    normSq_sub_le_via
      second third fourth
  have throughSecond :=
    normSq_sub_le_via
      first second fourth
  calc
    Basic.normSq (first - fourth) <=
        2 *
          (Basic.normSq (first - second) +
            Basic.normSq (second - fourth)) :=
      throughSecond
    _ <= 2 * (firstBound + 2 * (middleBound + lastBound)) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · apply add_le_add firstClose
        exact throughThird.trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add middleClose lastClose) (by decide))
      · decide

/-- Reversing the endpoints preserves Gaussian squared distance. -/
public theorem normSq_sub_symm
    (left right : Basic.Canonical) :
    Basic.normSq (left - right) =
      Basic.normSq (right - left) := by
  rw [show left - right = -(right - left) by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.neg_re,
        Basic.neg_im] <;> ring1,
    Norm.Basic.normSq_neg]

end Purelib.Data.Gaussian.Norm.Bounds
