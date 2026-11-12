module
public import Mathlib.Data.List.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-!
# Finite box conditions along a rational curve

A rational curve is stored homogeneously as `N(t) / D(t)`.  On every
displayed parameter where `D(t)` is nonzero, membership of the affine point
in a rational box is equivalent to four nonnegative univariate polynomial
evaluations.  The common positive factor is the explicitly displayed
quadrance `normSq (D(t))`, so no denominator sign choice or square root is
needed.

The nonzero members of the four-polynomial family are also collected into a
single finite product guard.  A later common Sturm subdivision can therefore
cut once while preserving all box-edge signs; identically-zero edge
conditions remain explicit instead of making the guard vanish.
-/

public section

namespace Purelib.RationalFunctions.Curve.Box

section
open Purelib.Data
section
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- Form the denominator-cleared left box inequality.

The polynomial is the real affine numerator minus the lower horizontal bound times denominator quadrance. -/
@[expose] def xLowerPolynomial (curve : RationalCurve) (box :
  Rational.Box) :
    (DensePolynomial Rat.Fraction.Rational) :=
  Coordinates.affineRealNumerator curve - DensePolynomial.scale box.xLower
    (Coordinates.denominatorNormSq curve)

/-- Form the denominator-cleared right box inequality.

The polynomial is the upper horizontal bound times denominator quadrance minus the real affine numerator. -/
@[expose] def xUpperPolynomial (curve : RationalCurve) (box :
  Rational.Box) :
    (DensePolynomial Rat.Fraction.Rational) :=
  DensePolynomial.scale box.xUpper (Coordinates.denominatorNormSq curve) -
    Coordinates.affineRealNumerator curve

/-- Form the denominator-cleared bottom box inequality.

The polynomial is the imaginary affine numerator minus the lower vertical bound times denominator quadrance. -/
@[expose] def yLowerPolynomial (curve : RationalCurve) (box :
  Rational.Box) :
    (DensePolynomial Rat.Fraction.Rational) :=
  Coordinates.affineImaginaryNumerator curve - DensePolynomial.scale box.yLower
    (Coordinates.denominatorNormSq curve)

/-- Form the denominator-cleared top box inequality.

The polynomial is the upper vertical bound times denominator quadrance minus the imaginary affine numerator. -/
@[expose] def yUpperPolynomial (curve : RationalCurve) (box :
  Rational.Box) :
    (DensePolynomial Rat.Fraction.Rational) :=
  DensePolynomial.scale box.yUpper (Coordinates.denominatorNormSq curve) -
    Coordinates.affineImaginaryNumerator curve

/-- List the four denominator-cleared box inequalities in left, right, bottom and top order. -/
@[expose] def conditionPolynomials (curve : RationalCurve) (box :
  Rational.Box) :
    List (DensePolynomial Rat.Fraction.Rational) :=
  [xLowerPolynomial curve box, xUpperPolynomial curve box,
    yLowerPolynomial curve box, yUpperPolynomial curve box]

/-- Prepend denominator quadrance to the four cleared box-condition polynomials.

The retained order is pole polynomial, left, right, bottom and top. This keeps the homogeneous denominator condition
explicit alongside the affine edge conditions. -/
@[expose] def profiledConditionPolynomials (curve : RationalCurve) (box
  : Rational.Box) :
    List (DensePolynomial Rat.Fraction.Rational) :=
  Coordinates.denominatorNormSq curve :: conditionPolynomials curve box

end

section
open Purelib.Geometry
open Purelib.RationalFunctions
/-- All four cleared box-condition polynomials are nonnegative at the displayed parameter. -/
@[expose] def Holds (curve : RationalCurve) (box :
  Rational.Box) (parameter : Rat.Fraction.Rational) : Prop :=
  0 <= (xLowerPolynomial curve box).eval parameter /\
    0 <= (xUpperPolynomial curve box).eval parameter /\
    0 <= (yLowerPolynomial curve box).eval parameter /\
    0 <= (yUpperPolynomial curve box).eval parameter

/-- All four cleared box-condition polynomials are positive at the displayed parameter. -/
@[expose] def StrictHolds
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational) : Prop :=
  0 < (xLowerPolynomial curve box).eval parameter /\
    0 < (xUpperPolynomial curve box).eval parameter /\
    0 < (yLowerPolynomial curve box).eval parameter /\
    0 < (yUpperPolynomial curve box).eval parameter

/-- Every polynomial in the ordered four-condition list evaluates nonnegatively. -/
@[expose] def ListedHolds
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational) : Prop :=
  Holds curve box parameter

/-- Every polynomial in the denominator-and-box condition list evaluates nonnegatively. -/
@[expose] def ProfiledListedHolds
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational) : Prop :=
  0 ≤ (Coordinates.denominatorNormSq curve).eval parameter ∧
    ListedHolds curve box parameter

/-- The list-shaped and conjunctive weak box predicates are equivalent. -/
theorem listedHolds_iff_holds
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational) :
    ListedHolds curve box parameter ↔ Holds curve box parameter := by
  rfl

/-- Prepending the denominator quadrance does not change the weak box predicate.

Its evaluation is a Gaussian quadrance and is always nonnegative, including at a pole. -/
theorem profiledListedHolds_iff_listedHolds
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational) :
    ProfiledListedHolds curve box parameter ↔
      ListedHolds curve box parameter := by
  constructor
  · exact And.right
  · intro holds
    exact ⟨by
      rewrite [Coordinates.eval_denominatorNormSq]
      exact Gaussian.Norm.Basic.normSq_nonneg _, holds⟩

end

section
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- At a nonzero denominator, the left condition evaluates to denominator quadrance times the corresponding coordinate
gap. -/
@[simp] theorem eval_xLowerPolynomial
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (xLowerPolynomial curve box).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) *
        ((curve.point parameter).re - box.xLower) := by
  simp only [xLowerPolynomial, DensePolynomial.eval_sub, DensePolynomial.eval_scale,
    Coordinates.eval_affineRealNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    Coordinates.eval_denominatorNormSq, -eq_self, -iff_self]
  ring1

/-- At a nonzero denominator, the right condition evaluates to denominator quadrance times the corresponding coordinate
gap. -/
@[simp] theorem eval_xUpperPolynomial
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (xUpperPolynomial curve box).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) *
        (box.xUpper - (curve.point parameter).re) := by
  simp only [xUpperPolynomial, DensePolynomial.eval_sub, DensePolynomial.eval_scale,
    Coordinates.eval_affineRealNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    Coordinates.eval_denominatorNormSq, -eq_self, -iff_self]
  ring1

/-- At a nonzero denominator, the bottom condition evaluates to denominator quadrance times the corresponding coordinate
gap. -/
@[simp] theorem eval_yLowerPolynomial
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (yLowerPolynomial curve box).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) *
        ((curve.point parameter).im - box.yLower) := by
  simp only [yLowerPolynomial, DensePolynomial.eval_sub, DensePolynomial.eval_scale,
    Coordinates.eval_affineImaginaryNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    Coordinates.eval_denominatorNormSq, -eq_self, -iff_self]
  ring1

/-- At a nonzero denominator, the top condition evaluates to denominator quadrance times the corresponding coordinate
gap. -/
@[simp] theorem eval_yUpperPolynomial
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (yUpperPolynomial curve box).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) *
        (box.yUpper - (curve.point parameter).im) := by
  simp only [yUpperPolynomial, DensePolynomial.eval_sub, DensePolynomial.eval_scale,
    Coordinates.eval_affineImaginaryNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    Coordinates.eval_denominatorNormSq, -eq_self, -iff_self]
  ring1

end

open Purelib.Geometry
open Purelib.RationalFunctions
/-- At a nonzero denominator, the cleared weak signs are equivalent to closed-box membership.

The common denominator quadrance is strictly positive. Cancelling it from all four coordinate inequalities recovers the
affine point's box bounds. -/
theorem holds_iff_contains
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    Holds curve box parameter ↔ box.Contains (curve.point parameter) := by
  let denominatorNorm := Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter)
  have denominatorPositive : 0 < denominatorNorm :=
    Gaussian.Norm.Basic.normSq_pos denominatorNonzero
  simp only [Holds, Rational.Box.Contains,
    eval_xLowerPolynomial curve box parameter denominatorNonzero,
    eval_xUpperPolynomial curve box parameter denominatorNonzero,
    eval_yLowerPolynomial curve box parameter denominatorNonzero,
    eval_yUpperPolynomial curve box parameter denominatorNonzero, -eq_self, -iff_self]
  have unscale {gap : Rat.Fraction.Rational}
      (cleared : 0 ≤ denominatorNorm * gap) : 0 ≤ gap := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := denominatorNorm) ?_ denominatorPositive
    calc
      0 * denominatorNorm = 0 := Rat.Fraction.Field.zero_mul_direct _
      _ ≤ denominatorNorm * gap := cleared
      _ = gap * denominatorNorm := by ring1
  constructor
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      Arithmetic.le_of_sub_nonneg_direct (unscale left),
      Arithmetic.le_of_sub_nonneg_direct (unscale right),
      Arithmetic.le_of_sub_nonneg_direct (unscale bottom),
      Arithmetic.le_of_sub_nonneg_direct (unscale top)⟩
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      Arithmetic.mul_nonneg_direct denominatorPositive.le
        (Arithmetic.sub_nonneg_direct left),
      Arithmetic.mul_nonneg_direct denominatorPositive.le
        (Arithmetic.sub_nonneg_direct right),
      Arithmetic.mul_nonneg_direct denominatorPositive.le
        (Arithmetic.sub_nonneg_direct bottom),
      Arithmetic.mul_nonneg_direct denominatorPositive.le
        (Arithmetic.sub_nonneg_direct top)⟩

/-- At a nonzero denominator, the cleared strict signs are equivalent to membership in the box interior.

Strict positivity of the common denominator quadrance preserves the four strict coordinate inequalities. -/
theorem strictHolds_iff_strictContains
    (curve : RationalCurve) (box : Rational.Box) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    StrictHolds curve box parameter ↔
      box.StrictContains (curve.point parameter) := by
  let denominatorNorm := Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter)
  have denominatorPositive : 0 < denominatorNorm :=
    Gaussian.Norm.Basic.normSq_pos denominatorNonzero
  simp only [StrictHolds, Rational.Box.StrictContains,
    eval_xLowerPolynomial curve box parameter denominatorNonzero,
    eval_xUpperPolynomial curve box parameter denominatorNonzero,
    eval_yLowerPolynomial curve box parameter denominatorNonzero,
    eval_yUpperPolynomial curve box parameter denominatorNonzero, -eq_self, -iff_self]
  constructor
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      Arithmetic.lt_of_sub_pos_direct
        (Arithmetic.pos_of_mul_pos_right_direct
          left denominatorPositive.le),
      Arithmetic.lt_of_sub_pos_direct
        (Arithmetic.pos_of_mul_pos_right_direct
          right denominatorPositive.le),
      Arithmetic.lt_of_sub_pos_direct
        (Arithmetic.pos_of_mul_pos_right_direct
          bottom denominatorPositive.le),
      Arithmetic.lt_of_sub_pos_direct
        (Arithmetic.pos_of_mul_pos_right_direct
          top denominatorPositive.le)⟩
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      Arithmetic.mul_pos_direct denominatorPositive
        (Arithmetic.sub_pos_direct left),
      Arithmetic.mul_pos_direct denominatorPositive
        (Arithmetic.sub_pos_direct right),
      Arithmetic.mul_pos_direct denominatorPositive
        (Arithmetic.sub_pos_direct bottom),
      Arithmetic.mul_pos_direct denominatorPositive
        (Arithmetic.sub_pos_direct top)⟩
end

end Purelib.RationalFunctions.Curve.Box

end
