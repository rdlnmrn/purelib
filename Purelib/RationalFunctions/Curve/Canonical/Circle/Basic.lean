module
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Quadratic.Identities
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.RationalFunctions.Curve.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Semiring.Normalization

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
open Purelib.Algebra

section
public section

/-!
# Canonical rational line and circle parameterizations

The CCL branch boundaries originate as coordinate lines or centered norm
circles before finite homographic pullback.  These explicit parameterizations
retain that provenance, including a proof that their parameter denominator
never vanishes.  Homographic transformation can subsequently move them into
the original polynomial coordinate.
-/

namespace Purelib.RationalFunctions.Curve.Canonical.Circle

/-- Parameterize the centered circle through a Gaussian base using a finite stereographic chart.

The numerator is base times the pair one minus parameter squared and twice the parameter; the denominator is parameter
squared plus one. The opposite base is the primary chart's exceptional point when the base is nonzero. -/
@[expose] def circle (base : Canonical) : Curve.RationalCurve where
  numerator :=
    ⟨[-base, (Gaussian.Cast.CurveCanonical.ofCoordinate 2 * Gaussian.Constants.imaginaryUnit) * base, base]⟩
  denominator := ⟨[1, 0, 1]⟩

/-- The primary circle numerator is the base times the displayed stereographic direction.

The finite Horner numerator retains the same Gaussian base and stereographic direction at the rational parameter. -/
@[simp] theorem circle_numeratorAt (base : Canonical) (parameter : Rational) :
    (circle base).numeratorAt parameter =
      base * ⟨1 - parameter ^ 2, 2 * parameter⟩ := by
  apply Gaussian.Basic.ext <;>
    simp [circle, Curve.RationalCurve.numeratorAt,
      Gaussian.Cast.Path.ofCoordinate,
      DensePolynomial.eval,
      DensePolynomial.evalCoeffs,
      Gaussian.Constants.imaginaryUnit, Gaussian.Cast.CurveCanonical.ofCoordinate, -sub_zero, -tsub_zero, -neg_sub,
        -eq_self, -iff_self] <;>
    ring1

/-- The primary circle denominator has real part parameter squared plus one. -/
theorem circle_denominatorAt_re
    (base : Canonical) (parameter : Rational) :
    ((circle base).denominatorAt parameter).re = parameter ^ 2 + 1 := by
  change
    (((((0 : Canonical) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).re) =
      parameter ^ 2 + 1
  simp only [Gaussian.Basic.zero_mul,
    Gaussian.Basic.zero_add,
    _root_.one_mul,
    Gaussian.Basic.add_zero,
    Gaussian.Basic.add_re,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.one_re]
  ring1

/-- The primary circle denominator has zero imaginary part. -/
theorem circle_denominatorAt_im
    (base : Canonical) (parameter : Rational) :
    ((circle base).denominatorAt parameter).im = 0 := by
  change
    (((((0 : Canonical) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).im) = 0
  simp only [Gaussian.Basic.zero_mul,
    Gaussian.Basic.zero_add,
    _root_.one_mul,
    Gaussian.Basic.add_zero,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.one_im]
  ring1

/-- The primary circle denominator is the real Gaussian parameter squared plus one. -/
@[simp] theorem circle_denominatorAt
    (base : Canonical) (parameter : Rational) :
    (circle base).denominatorAt parameter =
      ⟨parameter ^ 2 + 1, 0⟩ :=
  Gaussian.Basic.ext
    (circle_denominatorAt_re base parameter)
    (circle_denominatorAt_im base parameter)

/-- The primary circle denominator is nonzero at every rational parameter. -/
theorem circle_denominator_ne (base : Canonical) (parameter : Rational) :
    (circle base).denominatorAt parameter ≠ 0 := by
  rw [circle_denominatorAt]
  intro denominatorZero
  have realZero := congrArg Gaussian.Basic.re denominatorZero
  have positive : 0 < parameter ^ 2 + 1 :=
    lt_of_le_of_lt
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter)
      (by
        have := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
          (show (0 : Rational) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := this)
  change parameter ^ 2 + 1 = 0 at realZero
  rw [realZero] at positive
  exact (lt_irrefl 0 positive).elim

/-- Every primary-chart point has the same quadrance as the supplied base.

The primary direction and real denominator have equal positive quadrance, so the retained Gaussian quotient preserves
the base quadrance. -/
theorem normSq_circle_point (base : Canonical) (parameter : Rational) :
    Canonical.normSq ((circle base).point parameter) = Canonical.normSq base := by
  let direction : Canonical := ⟨1 - parameter ^ 2, 2 * parameter⟩
  let denominatorValue : Canonical := ⟨parameter ^ 2 + 1, 0⟩
  have directionNorm : Canonical.normSq direction = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [direction, Canonical.normSq]
    simp only [← pow_two, -eq_self, -iff_self]
    rw [Semiring.Normalization.product_pow]
    have twoSquared : (2 : Rational) ^ 2 = 4 := by decide
    rw [twoSquared]
    calc
      (1 - parameter ^ 2) ^ 2 + 4 * parameter ^ 2 =
          (1 - parameter ^ 2) ^ 2 + 4 * 1 * parameter ^ 2 := by
        rw [Rat.Fraction.Field.mul_one_direct]
      _ = (1 + parameter ^ 2) ^ 2 :=
        Rat.Quadratic.sub_square_add_four_product 1 (parameter ^ 2)
      _ = (parameter ^ 2 + 1) ^ 2 := by
        rw [Rat.Fraction.Field.add_comm]
  have denominatorNorm :
      Canonical.normSq denominatorValue = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [denominatorValue, Canonical.normSq]
    simp only [← pow_two, -eq_self, -iff_self]
    ring1
  have denominatorNonzero : denominatorValue ≠ 0 := by
    simpa only [circle_denominatorAt] using
      circle_denominator_ne base parameter
  have denominatorNormNonzero : Canonical.normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero ((Canonical.normSq_eq_zero denominatorValue).mp zero)
  have displayedNormNonzero : (parameter ^ 2 + 1) ^ 2 ≠ 0 := by
    rw [← denominatorNorm]
    exact denominatorNormNonzero
  rw [Curve.RationalCurve.point,
    circle_numeratorAt, circle_denominatorAt]
  change Canonical.normSq ((base * direction) * denominatorValue⁻¹) = Canonical.normSq
    base
  rw [Canonical.normSq_mul, Canonical.normSq_mul]
  rw [Canonical.normSq_inv denominatorValue denominatorNonzero,
    directionNorm, denominatorNorm,
    Rat.Fraction.Field.mul_assoc,
    Rat.Fraction.Field.mul_inv_cancel _ displayedNormNonzero,
    Rat.Fraction.Field.mul_one_direct]

/-! ## Reciprocal circle chart -/

/-- Parameterize the same centered circle using its reciprocal stereographic chart.

The numerator is base times the pair parameter squared minus one and twice the parameter, with denominator parameter
squared plus one. Parameter zero gives the primary chart's exceptional point, the negative base. -/
@[expose] def reciprocalCircle (base : Canonical) : Curve.RationalCurve where
  numerator :=
    ⟨[base, (Gaussian.Cast.CurveCanonical.ofCoordinate 2 * Gaussian.Constants.imaginaryUnit) * base, -base]⟩
  denominator := ⟨[1, 0, 1]⟩

/-- The reciprocal circle numerator is the base times the displayed reciprocal direction.

The finite Horner numerator retains the same Gaussian base and reciprocal stereographic direction at the rational
parameter. -/
@[simp] theorem reciprocalCircle_numeratorAt
    (base : Canonical) (parameter : Rational) :
    (reciprocalCircle base).numeratorAt parameter =
      base * ⟨parameter ^ 2 - 1, 2 * parameter⟩ := by
  apply Gaussian.Basic.ext <;>
    simp [reciprocalCircle,
      Curve.RationalCurve.numeratorAt,
      Gaussian.Cast.Path.ofCoordinate,
      DensePolynomial.eval,
      DensePolynomial.evalCoeffs,
      Gaussian.Constants.imaginaryUnit, Gaussian.Cast.CurveCanonical.ofCoordinate, -sub_zero, -tsub_zero, -eq_self,
        -iff_self] <;>
    ring1

/-- The reciprocal circle denominator has real part parameter squared plus one. -/
theorem reciprocalCircle_denominatorAt_re
    (base : Canonical) (parameter : Rational) :
    ((reciprocalCircle base).denominatorAt parameter).re =
      parameter ^ 2 + 1 := by
  change
    (((((0 : Canonical) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).re) =
      parameter ^ 2 + 1
  simp only [Gaussian.Basic.zero_mul,
    Gaussian.Basic.zero_add,
    _root_.one_mul,
    Gaussian.Basic.add_zero,
    Gaussian.Basic.add_re,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.one_re]
  ring1

/-- The reciprocal circle denominator has zero imaginary part. -/
theorem reciprocalCircle_denominatorAt_im
    (base : Canonical) (parameter : Rational) :
    ((reciprocalCircle base).denominatorAt parameter).im = 0 := by
  change
    (((((0 : Canonical) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).im) = 0
  simp only [Gaussian.Basic.zero_mul,
    Gaussian.Basic.zero_add,
    _root_.one_mul,
    Gaussian.Basic.add_zero,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.one_im]
  ring1

/-- The reciprocal circle denominator is the real Gaussian parameter squared plus one. -/
@[simp] theorem reciprocalCircle_denominatorAt
    (base : Canonical) (parameter : Rational) :
    (reciprocalCircle base).denominatorAt parameter =
      ⟨parameter ^ 2 + 1, 0⟩ :=
  Gaussian.Basic.ext
    (reciprocalCircle_denominatorAt_re base parameter)
    (reciprocalCircle_denominatorAt_im base parameter)

/-- The reciprocal circle denominator is nonzero at every rational parameter. -/
theorem reciprocalCircle_denominator_ne
    (base : Canonical) (parameter : Rational) :
    (reciprocalCircle base).denominatorAt parameter ≠ 0 := by
  rw [reciprocalCircle_denominatorAt]
  intro denominatorZero
  have realZero := congrArg Gaussian.Basic.re
    denominatorZero
  have positive : 0 < parameter ^ 2 + 1 :=
    lt_of_le_of_lt
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter)
      (by
        have := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
          (show (0 : Rational) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := this)
  change parameter ^ 2 + 1 = 0 at realZero
  rw [realZero] at positive
  exact (lt_irrefl 0 positive).elim

/-- Parameter zero in the reciprocal chart gives the negative base. -/
@[simp] theorem reciprocalCircle_point_zero (base : Canonical) :
    (reciprocalCircle base).point 0 = -base := by
  rw [Curve.RationalCurve.point,
    reciprocalCircle_numeratorAt, reciprocalCircle_denominatorAt]
  change (base * ⟨-1, 0⟩) * (1 : Canonical)⁻¹ = -base
  have inverseOne : (1 : Canonical)⁻¹ = 1 :=
    Gaussian.Field.inv_one_direct
  rw [inverseOne, Gaussian.Basic.mul_one]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im] <;>
    ring1

/-- Every reciprocal-chart point has the same quadrance as the supplied base.

The reciprocal direction and real denominator have equal positive quadrance, so the retained Gaussian quotient preserves
the base quadrance. -/
theorem normSq_reciprocalCircle_point
    (base : Canonical) (parameter : Rational) :
    Canonical.normSq ((reciprocalCircle base).point parameter) = Canonical.normSq base :=
      by
  let direction : Canonical := ⟨parameter ^ 2 - 1, 2 * parameter⟩
  let denominatorValue : Canonical := ⟨parameter ^ 2 + 1, 0⟩
  have directionNorm : Canonical.normSq direction = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [direction, Canonical.normSq]
    simp only [← pow_two, -eq_self, -iff_self]
    rw [Semiring.Normalization.product_pow]
    have twoSquared : (2 : Rational) ^ 2 = 4 := by decide
    rw [twoSquared]
    calc
      (parameter ^ 2 - 1) ^ 2 + 4 * parameter ^ 2 =
          (parameter ^ 2 - 1) ^ 2 + 4 * parameter ^ 2 * 1 := by
        rw [Rat.Fraction.Field.mul_one_direct]
      _ = (parameter ^ 2 + 1) ^ 2 :=
        Rat.Quadratic.sub_square_add_four_product (parameter ^ 2) 1
  have denominatorNorm :
      Canonical.normSq denominatorValue = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [denominatorValue, Canonical.normSq]
    simp only [← pow_two, -eq_self, -iff_self]
    ring1
  have denominatorNonzero : denominatorValue ≠ 0 := by
    simpa only [reciprocalCircle_denominatorAt] using
      reciprocalCircle_denominator_ne base parameter
  have denominatorNormNonzero : Canonical.normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero ((Canonical.normSq_eq_zero denominatorValue).mp zero)
  have displayedNormNonzero : (parameter ^ 2 + 1) ^ 2 ≠ 0 := by
    rw [← denominatorNorm]
    exact denominatorNormNonzero
  rw [Curve.RationalCurve.point,
    reciprocalCircle_numeratorAt, reciprocalCircle_denominatorAt]
  change Canonical.normSq ((base * direction) * denominatorValue⁻¹) = Canonical.normSq
    base
  rw [Canonical.normSq_mul, Canonical.normSq_mul]
  rw [Canonical.normSq_inv denominatorValue denominatorNonzero,
    directionNorm, denominatorNorm,
    Rat.Fraction.Field.mul_assoc,
    Rat.Fraction.Field.mul_inv_cancel _ displayedNormNonzero,
    Rat.Fraction.Field.mul_one_direct]

/-- Each primary-chart point is the base times the corresponding unit-base point. -/
theorem circle_point_scale
    (base : Canonical) (parameter : Rational) :
    (circle base).point parameter =
      base * (circle 1).point parameter := by
  rw [Curve.RationalCurve.point,
    Curve.RationalCurve.point,
    circle_numeratorAt, circle_numeratorAt,
    circle_denominatorAt, circle_denominatorAt]
  rw [_root_.one_mul,
    Gaussian.Basic.mul_assoc]

/-- Each reciprocal-chart point is the base times the corresponding unit-base point. -/
theorem reciprocalCircle_point_scale
    (base : Canonical) (parameter : Rational) :
    (reciprocalCircle base).point parameter =
      base * (reciprocalCircle 1).point parameter := by
  rw [Curve.RationalCurve.point,
    Curve.RationalCurve.point,
    reciprocalCircle_numeratorAt, reciprocalCircle_numeratorAt,
    reciprocalCircle_denominatorAt, reciprocalCircle_denominatorAt]
  rw [_root_.one_mul,
    Gaussian.Basic.mul_assoc]
end Purelib.RationalFunctions.Curve.Canonical.Circle

end
