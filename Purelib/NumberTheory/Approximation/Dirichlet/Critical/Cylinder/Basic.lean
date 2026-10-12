module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Data

open Purelib.Data.Rat

section

/-!
# Critical rational cylinders

The parameter polynomial defines the open rational chamber. Scaled Gaussian
coordinates reduce its finite unit and diagonal coefficient alternatives to
explicit positive rational polynomials, retaining the original coefficient data.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic

/-- The scalar boundary polynomial used by the critical rational family. -/
@[expose] def parameterPolynomial (value :
  Fraction.Rational) : Fraction.Rational :=
  value ^ 2 - 4 * value + 1

open Purelib.NumberTheory.Approximation in
/-- The useful open rational side of the critical parameter chamber. -/
@[expose] def IsCriticalParameter (value :
  Fraction.Rational) : Prop :=
  (1 / 4 : Fraction.Rational) ≤ value ∧ value < 1 / 3 ∧
    0 < parameterPolynomial value

/-- The rational number one half. -/
@[expose] def half : Fraction.Rational := 1
  / 2

section
open Purelib.NumberTheory.Approximation
/-- Twice the retained rational half is one. -/
theorem two_mul_half : (2 :
  Fraction.Rational) * half = 1 := by
  unfold half
  decide

/-- The retained rational half multiplied by two is one. -/
private theorem half_mul_two :
  half * (2 : Fraction.Rational) = 1 := by
  rw [Fraction.Field.mul_comm]
  exact two_mul_half

/-- The square of the rational half multiplied by four is one. -/
private theorem half_sq_mul_four :
  half ^ 2 * (4 : Fraction.Rational) = 1 := by
  unfold half
  decide

/-- Four times the square of the rational half is one. -/
theorem four_mul_half_sq : (4 :
  Fraction.Rational) * half ^ 2 = 1 := by
  rw [Fraction.Field.mul_comm]
  exact half_sq_mul_four

/-- The square of the rational half is one quarter. -/
private theorem half_sq :
  half ^ 2 = (1 / 4 : Fraction.Rational) := by
  unfold half
  decide

/-- Squaring a rational half multiple scales the square by one quarter. -/
private theorem half_mul_sq (value :
  Fraction.Rational) :
    (half * value) ^ 2 = (1 / 4 : Fraction.Rational) * value ^ 2 := by
  calc
    (half * value) ^ 2 = half ^ 2 * value ^ 2 := by
      ring1
    _ = (1 / 4 : Fraction.Rational) * value ^ 2 := by rw [half_sq]

end

/-- The normalized upper error at critical parameter `value`. -/
@[expose] def criticalErrorRatio (value :
  Fraction.Rational) : Gaussian.Basic.Canonical :=
  ⟨1 / 2, (1 / 2 : Fraction.Rational) * value⟩

/-- The normalized lower denominator at critical parameter `value`. -/
@[expose] def criticalDenominatorRatio
  (value : Fraction.Rational) : Gaussian.Basic.Canonical :=
  ⟨(1 / 2 : Fraction.Rational) * value, -(1 / 2 : Fraction.Rational)⟩

/-- The common quadrance of the two normalized critical coordinates. -/
@[expose] def criticalCoordinateNorm (value
  : Fraction.Rational) : Fraction.Rational :=
  (1 / 2 : Fraction.Rational) ^ 2 + ((1 / 2 : Fraction.Rational) * value) ^ 2

/-- The normalized form of one quarter of the boundary polynomial. -/
@[expose] def normalizedDefect (value :
  Fraction.Rational) : Fraction.Rational :=
  (1 / 2 : Fraction.Rational) ^ 2 - 2 * (1 / 2 : Fraction.Rational) * value +
    ((1 / 2 : Fraction.Rational) * value) ^ 2

section
open Purelib.NumberTheory.Approximation
/-- The normalized determinant gap of the critical rational family. -/
@[expose] def criticalGap (value :
  Fraction.Rational) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (1 - criticalDenominatorRatio value *
    criticalErrorRatio value)

/-- The critical error ratio has the displayed common coordinate quadrance. -/
theorem normSq_criticalErrorRatio (value :
  Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (criticalErrorRatio value) =
      criticalCoordinateNorm value := by
  unfold criticalErrorRatio criticalCoordinateNorm
    Data.Gaussian.Norm.Basic.normSq
  rfl

/-- The critical denominator ratio has the displayed common coordinate quadrance. -/
theorem normSq_criticalDenominatorRatio
  (value : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (criticalDenominatorRatio value) =
      criticalCoordinateNorm value := by
  unfold criticalDenominatorRatio
    criticalCoordinateNorm Data.Gaussian.Norm.Basic.normSq
  change (half * value) ^ 2 + (-half) ^ 2 =
    half ^ 2 + (half * value) ^ 2
  ring1

/-- Expand the critical determinant gap as a sum of two rational squares. -/
theorem criticalGap_eq (value :
  Fraction.Rational) :
    criticalGap value =
      (1 - 2 * (1 / 2 : Fraction.Rational) ^ 2 * value) ^ 2 +
        ((1 / 2 : Fraction.Rational) ^ 2 - ((1 / 2 : Fraction.Rational) * value) ^ 2) ^ 2 := by
  unfold criticalGap criticalErrorRatio
    criticalDenominatorRatio Data.Gaussian.Norm.Basic.normSq
  simp only [Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.one_re,
    Gaussian.Basic.one_im, -eq_self, -iff_self]
  ring1

/-- Four times the normalized defect is the parameter boundary polynomial. -/
theorem normalizedDefect_mul_four (value :
  Fraction.Rational) :
    normalizedDefect value * 4 = parameterPolynomial
      value := by
  calc
    normalizedDefect value * 4 =
        half ^ 2 * 4 - 4 * (2 * half) * value +
          half ^ 2 * 4 * value ^ 2 := by
      unfold normalizedDefect
      simp only [half, -eq_self, -iff_self]
      ring1
    _ = parameterPolynomial value := by
      rw [two_mul_half, half_sq_mul_four]
      unfold parameterPolynomial
      ring1

/-- Every parameter in the critical chamber is nonnegative. -/
theorem criticalParameter_nonnegative
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 ≤ value :=
  (show (0 : Fraction.Rational) ≤ 1 / 4 by decide).trans certificate.1

/-- Every parameter in the critical chamber is at most one third. -/
private theorem
  criticalParameter_le_oneThird
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    value ≤ 1 / 3 := certificate.2.1.le

/-- The common critical coordinate quadrance is below one throughout the critical chamber. -/
theorem criticalCoordinateNorm_lt_one
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    criticalCoordinateNorm value < 1 := by
  have valueNonnegative := criticalParameter_nonnegative certificate
  have scaledBound : half * value ≤ half * (1 / 3 :
    Fraction.Rational) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (criticalParameter_le_oneThird certificate)
      (show (0 : Fraction.Rational) ≤ half by
        unfold half; decide)
  have squareBound : (half * value) ^ 2 ≤
      (half * (1 / 3 : Fraction.Rational)) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (show (0 : Fraction.Rational) ≤ half by
          unfold half; decide)
        valueNonnegative)
      scaledBound 2
  calc
    criticalCoordinateNorm value =
        half ^ 2 + (half * value) ^ 2 := rfl
    _ = (half * value) ^ 2 + half ^ 2 := by ring1
    _ ≤ (half * (1 / 3 : Fraction.Rational)) ^ 2 +
      half ^ 2 :=
      add_le_add_left squareBound _
    _ = half ^ 2 + (half * (1 / 3 :
      Fraction.Rational)) ^ 2 := by
      ring1
    _ < 1 := by decide

/-- The common critical coordinate quadrance is nonnegative. -/
private theorem
  criticalCoordinateNorm_nonnegative (value
  : Fraction.Rational) :
    0 ≤ criticalCoordinateNorm value := by
  unfold criticalCoordinateNorm
  exact add_nonneg
    (Fraction.Order.Arithmetic.sq_nonneg_direct half)
    (Fraction.Order.Arithmetic.sq_nonneg_direct (half * value))

/-- The common critical coordinate quadrance is positive for every rational parameter. -/
private theorem criticalCoordinateNorm_pos
  (value : Fraction.Rational) :
    0 < criticalCoordinateNorm value := by
  calc
    (0 : Fraction.Rational) < half ^ 2 := by
      rw [half_sq]; decide
    _ ≤ half ^ 2 + (half * value) ^ 2 :=
      le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.sq_nonneg_direct (half * value))
    _ = criticalCoordinateNorm value := rfl

/-- The elementary coefficient estimate below has genuine slack throughout
the finite critical chamber.  This replaces a compactness or shortest-vector
argument by the displayed quartic margin `7 - 16*s + s^4`. -/
private theorem
  twice_one_add_coordinateNorm_lt_four_gap
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    2 * (1 + criticalCoordinateNorm value) < 4 *
      criticalGap value := by
  have scaledParameter : 16 * value < 16 * (1 / 3 : Fraction.Rational) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 16 by decide) certificate.2.1
  have sixteenValueLtSeven : 16 * value < (7 : Fraction.Rational) :=
    scaledParameter.trans (by decide)
  have linearMargin : 0 < 7 - 16 * value :=
    Fraction.Order.Arithmetic.sub_pos_direct sixteenValueLtSeven
  have quarticNonnegative : 0 ≤ value ^ 4 :=
    Fraction.Order.Arithmetic.pow_nonneg_direct
      (criticalParameter_nonnegative certificate) 4
  have quarticMargin : 0 < 7 - 16 * value + value ^ 4 :=
    linearMargin.trans_le (le_add_of_nonneg_right quarticNonnegative)
  apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Fraction.Rational) * 4 = 0 := by ring1
      _ < 7 - 16 * value + value ^ 4 := quarticMargin
      _ =
          (4 * criticalGap value -
            2 * (1 + criticalCoordinateNorm value)) * 4 := by
        calc
          7 - 16 * value + value ^ 4 =
              (4 * criticalGap value -
                  2 * (1 + criticalCoordinateNorm value)) * 4 -
                (4 * half ^ 2 - 1) *
                  ((4 * half ^ 2 - 1) - 16 * value +
                    8 * half ^ 2 * value ^ 2 +
                    (4 * half ^ 2 + 1) * value ^ 4) := by
            rw [criticalGap_eq]
            unfold criticalCoordinateNorm
            simp only [half, -eq_self, -iff_self]
            ring1
          _ =
              (4 * criticalGap value -
                2 * (1 + criticalCoordinateNorm value)) * 4 := by
            rw [four_mul_half_sq]
            ring1
  · decide

/-- The critical determinant gap is positive throughout the parameter chamber.

The explicit quartic margin gives a strictly positive lower bound after multiplication by four. -/
theorem criticalGap_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < criticalGap value := by
  have positiveLeft :
      0 < 2 * (1 + criticalCoordinateNorm value) := by
    have onePositive :
        (0 : Fraction.Rational) < 1 + criticalCoordinateNorm value :=
      (show (0 : Fraction.Rational) < 1 by decide).trans_le
        (le_add_of_nonneg_right (criticalCoordinateNorm_nonnegative value))
    exact Fraction.Order.Arithmetic.mul_pos_direct (by decide) onePositive
  have positiveScaled : 0 < 4 * criticalGap value :=
    positiveLeft.trans
      (twice_one_add_coordinateNorm_lt_four_gap certificate)
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Fraction.Rational) * 4 = 0 := by ring1
      _ < 4 * criticalGap value := positiveScaled
      _ = criticalGap value * 4 := by ring1
  · decide

end

/-- Twice the real error coordinate, written as an integral-coefficient affine expression in the parameter. -/
private def scaledErrorReal
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  2 * (left.re : Fraction.Rational) + (right.re : Fraction.Rational) -
    (right.im : Fraction.Rational) * value

/-- Twice the imaginary error coordinate, written as an integral-coefficient affine expression in the parameter. -/
private def scaledErrorImaginary
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  2 * (left.im : Fraction.Rational) + (right.im : Fraction.Rational) +
    (right.re : Fraction.Rational) * value

/-- Twice the real denominator coordinate, written as an integral-coefficient affine expression in the parameter. -/
private def scaledDenominatorReal
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  (left.re : Fraction.Rational) * value + (left.im : Fraction.Rational) +
    2 * (right.re : Fraction.Rational)

/-- Twice the imaginary denominator coordinate, written as an integral-coefficient affine expression in the parameter.
-/
private def scaledDenominatorImaginary
    (left right : GaussianInt) (value : Fraction.Rational) : Fraction.Rational :=
  -(left.re : Fraction.Rational) + (left.im : Fraction.Rational) * value +
    2 * (right.im : Fraction.Rational)

section
open Purelib.NumberTheory.Approximation
/-- The scaled real error formula agrees with twice the Gaussian error coordinate. -/
private theorem two_mul_error_real
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (GaussianInt.toGaussian left +
      GaussianInt.toGaussian right * criticalErrorRatio value).re =
        scaledErrorReal left right value := by
  simp only [criticalErrorRatio,
    Gaussian.Basic.add_re,
    Gaussian.Basic.mul_re, GaussianInt.toGaussian, -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * ((left.re : Fraction.Rational) +
        ((right.re : Fraction.Rational) * half -
          (right.im : Fraction.Rational) * (half * value))) =
      2 * (left.re : Fraction.Rational) +
        (2 * half) * (right.re : Fraction.Rational) -
          (2 * half) * (right.im : Fraction.Rational) * value := by ring1
    _ = scaledErrorReal left right value := by
      rw [two_mul_half]
      unfold scaledErrorReal
      ring1

/-- The scaled imaginary error formula agrees with twice the Gaussian error coordinate. -/
private theorem two_mul_error_imaginary
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (GaussianInt.toGaussian left +
      GaussianInt.toGaussian right * criticalErrorRatio value).im =
        scaledErrorImaginary left right value := by
  simp only [criticalErrorRatio,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_im, GaussianInt.toGaussian, -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * ((left.im : Fraction.Rational) +
        ((right.re : Fraction.Rational) * (half * value) +
          (right.im : Fraction.Rational) * half)) =
      2 * (left.im : Fraction.Rational) +
        (2 * half) * (right.im : Fraction.Rational) +
          (2 * half) * (right.re : Fraction.Rational) * value := by ring1
    _ = scaledErrorImaginary left right value := by
      rw [two_mul_half]
      unfold scaledErrorImaginary
      ring1

/-- The scaled real denominator formula agrees with twice the Gaussian denominator coordinate. -/
private theorem two_mul_denominator_real
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (GaussianInt.toGaussian left * criticalDenominatorRatio value +
      GaussianInt.toGaussian right).re = scaledDenominatorReal left right value := by
  simp only [criticalDenominatorRatio,
    Gaussian.Basic.add_re,
    Gaussian.Basic.mul_re, GaussianInt.toGaussian, -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * (((left.re : Fraction.Rational) * (half * value) -
        (left.im : Fraction.Rational) * -half) + (right.re : Fraction.Rational)) =
      (2 * half) * (left.re : Fraction.Rational) * value +
        (2 * half) * (left.im : Fraction.Rational) +
          2 * (right.re : Fraction.Rational) := by ring1
    _ = scaledDenominatorReal left right value := by
      rw [two_mul_half]
      unfold scaledDenominatorReal
      ring1

/-- The scaled imaginary denominator formula agrees with twice the Gaussian denominator coordinate. -/
private theorem
  two_mul_denominator_imaginary
    (left right : GaussianInt) (value : Fraction.Rational) :
    2 * (GaussianInt.toGaussian left * criticalDenominatorRatio value +
      GaussianInt.toGaussian right).im =
        scaledDenominatorImaginary left right value := by
  simp only [criticalDenominatorRatio,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_im, GaussianInt.toGaussian, -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  calc
    2 * (((left.re : Fraction.Rational) * -half +
        (left.im : Fraction.Rational) * (half * value)) +
          (right.im : Fraction.Rational)) =
      -(2 * half) * (left.re : Fraction.Rational) +
        (2 * half) * (left.im : Fraction.Rational) * value +
          2 * (right.im : Fraction.Rational) := by ring1
    _ = scaledDenominatorImaginary left right value := by
      rw [two_mul_half]
      unfold scaledDenominatorImaginary
      ring1

/-- Four times the error quadrance excess over one is the scaled coordinate square sum minus four. -/
private theorem error_difference_mul_four
    (left right : GaussianInt) (value : Fraction.Rational) :
    (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
      GaussianInt.toGaussian right * criticalErrorRatio value) - 1) * 4 =
        scaledErrorReal left right value ^ 2 +
          scaledErrorImaginary left right value ^ 2 - 4 := by
  unfold Data.Gaussian.Norm.Basic.normSq
  calc
    (((GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value).re ^ 2 +
        (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value).im ^ 2) - 1) * 4 =
      (2 * (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * criticalErrorRatio value).re) ^ 2 +
      (2 * (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * criticalErrorRatio value).im) ^ 2 - 4 := by
          ring1
    _ = scaledErrorReal left right value ^ 2 +
        scaledErrorImaginary left right value ^ 2 - 4 := by
      rw [two_mul_error_real,
        two_mul_error_imaginary]

/-- Four times the denominator quadrance excess over one is the scaled coordinate square sum minus four. -/
private theorem
  denominator_difference_mul_four
    (left right : GaussianInt) (value : Fraction.Rational) :
    (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
      criticalDenominatorRatio value +
      GaussianInt.toGaussian right) - 1) * 4 =
        scaledDenominatorReal left right value ^ 2 +
          scaledDenominatorImaginary left right value ^ 2 - 4 := by
  unfold Data.Gaussian.Norm.Basic.normSq
  calc
    (((GaussianInt.toGaussian left * criticalDenominatorRatio value +
          GaussianInt.toGaussian right).re ^ 2 +
        (GaussianInt.toGaussian left * criticalDenominatorRatio value +
          GaussianInt.toGaussian right).im ^ 2) - 1) * 4 =
      (2 * (GaussianInt.toGaussian left * criticalDenominatorRatio value +
        GaussianInt.toGaussian right).re) ^ 2 +
      (2 * (GaussianInt.toGaussian left * criticalDenominatorRatio value +
        GaussianInt.toGaussian right).im) ^ 2 - 4 := by ring1
    _ = scaledDenominatorReal left right value ^ 2 +
        scaledDenominatorImaginary left right value ^ 2 - 4 := by
      rw [two_mul_denominator_real,
        two_mul_denominator_imaginary]

end

/-- A rational number is positive when its product with four is positive. -/
private theorem
  positive_of_mul_four_positive {value :
  Fraction.Rational}
    (scaledPositive : 0 < value * 4) : 0 < value := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Fraction.Rational) * 4 = 0 := by ring1
      _ < value * 4 := scaledPositive
  · decide

open Purelib.NumberTheory.Approximation in
/-- The polynomial `1 + 4s + s²` is positive throughout the critical chamber. -/
private theorem scaledPlus_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < 1 + 4 * value + value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + value ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (criticalParameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.sq_nonneg_direct value)
  exact (show (0 : Fraction.Rational) < 1 by decide).trans_le
    (by
      calc
        (1 : Fraction.Rational) ≤ 1 + (4 * value + value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 1 + 4 * value + value ^ 2 := by ring1)

/-- The polynomial `5 + s²` is positive for every rational parameter. -/
private theorem scaledFive_pos {value :
  Fraction.Rational} :
    0 < 5 + value ^ 2 :=
  (show (0 : Fraction.Rational) < 5 by decide).trans_le
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct value))

section
open Purelib.NumberTheory.Approximation
/-- The polynomial `6 + 4s + 2s²` is positive throughout the critical chamber. -/
private theorem scaledSixPlusFour_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < 6 + 4 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + 2 * value ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (criticalParameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct value))
  exact (show (0 : Fraction.Rational) < 6 by decide).trans_le
    (by
      calc
        (6 : Fraction.Rational) ≤ 6 + (4 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 4 * value + 2 * value ^ 2 := by ring1)

/-- The polynomial `9 - 4s + s²` is positive throughout the critical chamber. -/
private theorem scaledNineMinusFour_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < 9 - 4 * value + value ^ 2 := by
  calc
    (0 : Fraction.Rational) < 8 + parameterPolynomial value :=
      (show (0 : Fraction.Rational) < 8 by decide).trans_le
        (le_add_of_nonneg_right certificate.2.2.le)
    _ = 9 - 4 * value + value ^ 2 := by
      unfold parameterPolynomial
      ring1

end

/-- The polynomial `14 + 2s²` is positive for every rational parameter. -/
private theorem scaledFourteen_pos {value :
  Fraction.Rational} :
    0 < 14 + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 2 * value ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct value)
  exact (show (0 : Fraction.Rational) < 14 by decide).trans_le
    (le_add_of_nonneg_right tailNonnegative)

section
open Purelib.NumberTheory.Approximation
/-- The polynomial `6 - 8s + 2s²` is positive throughout the critical chamber. -/
private theorem scaledSixMinusEight_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < 6 - 8 * value + 2 * value ^ 2 := by
  have doubledNonnegative : 0 ≤ 2 * parameterPolynomial value :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      certificate.2.2.le
  calc
    (0 : Fraction.Rational) < 4 + 2 * parameterPolynomial value :=
      (show (0 : Fraction.Rational) < 4 by decide).trans_le
        (le_add_of_nonneg_right doubledNonnegative)
    _ = 6 - 8 * value + 2 * value ^ 2 := by
      unfold parameterPolynomial
      ring1

/-- The polynomial `6 + 8s + 2s²` is positive throughout the critical chamber. -/
private theorem scaledSixPlusEight_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < 6 + 8 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 8 * value + 2 * value ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (criticalParameter_nonnegative certificate))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct value))
  exact (show (0 : Fraction.Rational) < 6 by decide).trans_le
    (by
      calc
        (6 : Fraction.Rational) ≤ 6 + (8 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 8 * value + 2 * value ^ 2 := by ring1)

/-- The polynomial `1 - 4s + s²` is positive throughout the critical chamber. -/
private theorem scaledMinus_pos
    {value : Fraction.Rational} (certificate : IsCriticalParameter value) :
    0 < 1 - 4 * value + value ^ 2 := by
  calc
    (0 : Fraction.Rational) < parameterPolynomial value := certificate.2.2
    _ = 1 - 4 * value + value ^ 2 := by
      unfold parameterPolynomial
      ring1

end

/-- Normalize the displayed scaled Gaussian coordinates to rational polynomial identities.

The tactic expands only the four coordinate formulas and the canonical imaginary unit before ring normalization. -/
macro "scaled_ring" : tactic =>
  `(tactic| (simp only [Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.scaledErrorReal,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.scaledErrorImaginary,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.scaledDenominatorReal,
      Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.scaledDenominatorImaginary,
      Purelib.Data.GaussianInt.toGaussian,
      Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit,
      Purelib.Data.GaussianInt.one_re, Purelib.Data.GaussianInt.one_im,
      Purelib.Data.GaussianInt.zero_re, Purelib.Data.GaussianInt.zero_im,
      Purelib.Data.GaussianInt.add_re, Purelib.Data.GaussianInt.add_im,
      Purelib.Data.GaussianInt.mul_re, Purelib.Data.GaussianInt.mul_im,
      Purelib.Data.GaussianInt.neg_re, Purelib.Data.GaussianInt.neg_im,
      Purelib.Algebra.Ring.IntCast.neg,
      Purelib.Algebra.Ring.IntCast.cast_zero,
      Purelib.Algebra.Ring.IntCast.cast_negSucc,
      Int.cast_natCast, Int.cast_ofNat,
      Purelib.Data.Rat.Fraction.Arithmetic.sub_eq_add_neg_direct,
      -eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;> ring1))

/-- Prove a critical-cylinder exterior from its selected positive polynomial.

The generated finite cases select this schema directly; exact ring checking verifies the coordinate identity.
-/
macro "critical_error" positive:term : tactic =>
  `(tactic| first
    | left
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.lt_of_sub_pos_direct
      apply Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.positive_of_mul_four_positive
      rw [Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.error_difference_mul_four]
      convert ($positive) using 1 <;> scaled_ring)

/-- Prove a critical-cylinder exterior from its selected positive polynomial.

The generated finite cases select this schema directly; exact ring checking verifies the coordinate identity.
-/
macro "critical_denominator" positive:term : tactic =>
  `(tactic| first
    | right
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.lt_of_sub_pos_direct
      apply Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.positive_of_mul_four_positive
      rw [Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.denominator_difference_mul_four]
      convert ($positive) using 1 <;> scaled_ring)

open Purelib.NumberTheory.Approximation
/-- Two Gaussian unit coefficients give a strict error or denominator exterior.

The sixteen displayed unit combinations reduce to positive rational polynomials in the critical parameter chamber. -/
private theorem
  unit_unit_coefficients_strictly_exterior
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {left right : GaussianInt}
    (leftUnit : GaussianInt.Norm.Small.IsGaussianUnit left)
    (rightUnit : GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl <;>
    rcases rightUnit with rfl | rfl | rfl | rfl
  · critical_denominator (scaledPlus_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_denominator (scaledPlus_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_denominator (scaledPlus_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_denominator (scaledPlus_pos certificate)

/-- A unit leading coefficient and diagonal trailing coefficient give a strict cylinder exterior.

The sixteen displayed combinations are checked by the exact scaled coordinate identities. -/
private theorem
  unit_diagonal_coefficients_strictly_exterior
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {left right : GaussianInt}
    (leftUnit : GaussianInt.Norm.Small.IsGaussianUnit left)
    (rightDiagonal : GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl <;>
    rcases rightDiagonal with rfl | rfl | rfl | rfl
  · critical_denominator (scaledPlus_pos certificate)
  · critical_error (scaledSixPlusFour_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_denominator (scaledNineMinusFour_pos certificate)
  · critical_denominator (scaledNineMinusFour_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_error (scaledSixPlusFour_pos certificate)
  · critical_denominator (scaledPlus_pos certificate)
  · critical_error (scaledSixPlusFour_pos certificate)
  · critical_denominator (scaledNineMinusFour_pos certificate)
  · critical_denominator (scaledPlus_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_denominator (scaledMinus_pos certificate)
  · critical_denominator (scaledPlus_pos certificate)
  · critical_denominator (scaledNineMinusFour_pos certificate)
  · critical_error (scaledSixPlusFour_pos certificate)

/-- A diagonal leading coefficient and unit trailing coefficient give a strict cylinder exterior.

The sixteen displayed combinations are checked by the exact scaled coordinate identities. -/
private theorem
  diagonal_unit_coefficients_strictly_exterior
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {left right : GaussianInt}
    (leftDiagonal : GaussianInt.Norm.Small.IsDiagonal left)
    (rightUnit : GaussianInt.Norm.Small.IsGaussianUnit right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
    rcases rightUnit with rfl | rfl | rfl | rfl
  · critical_denominator (scaledSixPlusFour_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_error (scaledNineMinusFour_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_error (scaledNineMinusFour_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_denominator (scaledSixPlusFour_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_error (scaledNineMinusFour_pos certificate)
  · critical_denominator (scaledSixPlusFour_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_error (scaledMinus_pos certificate)
  · critical_denominator (scaledSixPlusFour_pos certificate)
  · critical_error (scaledPlus_pos certificate)
  · critical_error (scaledNineMinusFour_pos certificate)

/-- The leading coefficient `1 + i` with any diagonal trailing coefficient gives a strict cylinder exterior. -/
private theorem
  diagonal_diagonal_coefficients_strictly_exterior_left_0
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {right : GaussianInt}
    (rightDiagonal : GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right)  := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · critical_error (scaledFourteen_pos (value := value))
  · critical_denominator (scaledFourteen_pos (value := value))
  · critical_error (scaledSixMinusEight_pos certificate)
  · critical_denominator (scaledSixMinusEight_pos certificate)

/-- The leading coefficient `1 - i` with any diagonal trailing coefficient gives a strict cylinder exterior. -/
private theorem
  diagonal_diagonal_coefficients_strictly_exterior_left_1
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {right : GaussianInt}
    (rightDiagonal : GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨1, -1⟩ : GaussianInt) +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨1, -1⟩ : GaussianInt) *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right)  := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · critical_error (scaledSixMinusEight_pos certificate)
  · critical_error (scaledFourteen_pos (value := value))
  · critical_denominator (scaledSixMinusEight_pos certificate)
  · critical_denominator (scaledFourteen_pos (value := value))

/-- The leading coefficient `-1 + i` with any diagonal trailing coefficient gives a strict cylinder exterior. -/
private theorem
  diagonal_diagonal_coefficients_strictly_exterior_left_2
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {right : GaussianInt}
    (rightDiagonal : GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨-1, 1⟩ : GaussianInt) +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨-1, 1⟩ : GaussianInt) *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right)  := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · critical_denominator (scaledFourteen_pos (value := value))
  · critical_denominator (scaledSixMinusEight_pos certificate)
  · critical_error (scaledFourteen_pos (value := value))
  · critical_error (scaledSixMinusEight_pos certificate)

/-- The leading coefficient `-1 - i` with any diagonal trailing coefficient gives a strict cylinder exterior. -/
private theorem
  diagonal_diagonal_coefficients_strictly_exterior_left_3
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {right : GaussianInt}
    (rightDiagonal : GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨-1, -1⟩ : GaussianInt) +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (⟨-1, -1⟩ : GaussianInt) *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right)  := by
  rcases rightDiagonal with rfl | rfl | rfl | rfl
  · critical_denominator (scaledSixMinusEight_pos certificate)
  · critical_error (scaledSixMinusEight_pos certificate)
  · critical_denominator (scaledFourteen_pos (value := value))
  · critical_error (scaledFourteen_pos (value := value))

/-- Two diagonal coefficients give a strict error or denominator exterior throughout the critical chamber. -/
private theorem
  diagonal_diagonal_coefficients_strictly_exterior
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    {left right : GaussianInt}
    (leftDiagonal : GaussianInt.Norm.Small.IsDiagonal left)
    (rightDiagonal : GaussianInt.Norm.Small.IsDiagonal right) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl
  · exact diagonal_diagonal_coefficients_strictly_exterior_left_0 certificate
      rightDiagonal
  · exact diagonal_diagonal_coefficients_strictly_exterior_left_1 certificate
      rightDiagonal
  · exact diagonal_diagonal_coefficients_strictly_exterior_left_2 certificate
      rightDiagonal
  · exact diagonal_diagonal_coefficients_strictly_exterior_left_3 certificate
      rightDiagonal

/-- Nonzero Gaussian coefficients of quadrance below four give a strict cylinder exterior.

Each coefficient is a unit or diagonal, so the finite coordinate classifications cover all cases. -/
theorem
  small_nonzero_coefficients_strictly_exterior
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    (left right : GaussianInt)
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0)
    (leftSmall : GaussianInt.normNat left < 4) (rightSmall : GaussianInt.normNat right < 4) :
    (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) := by
  have leftShape :
      GaussianInt.Norm.Small.IsGaussianUnit left ∨
        GaussianInt.Norm.Small.IsDiagonal left := by
    rcases GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
        left leftSmall with zeroNorm | unitNorm | diagonalNorm
    · exact (leftNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero zeroNorm)).elim
    · exact Or.inl
        (GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm)
    · exact Or.inr
        (GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two diagonalNorm)
  have rightShape :
      GaussianInt.Norm.Small.IsGaussianUnit right ∨
        GaussianInt.Norm.Small.IsDiagonal right := by
    rcases GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
        right rightSmall with zeroNorm | unitNorm | diagonalNorm
    · exact (rightNonzero
        (GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero zeroNorm)).elim
    · exact Or.inl
        (GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm)
    · exact Or.inr
        (GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two diagonalNorm)
  rcases leftShape with leftUnit | leftDiagonal
  · rcases rightShape with rightUnit | rightDiagonal
    · exact unit_unit_coefficients_strictly_exterior
        certificate leftUnit rightUnit
    · exact unit_diagonal_coefficients_strictly_exterior
        certificate leftUnit rightDiagonal
  · rcases rightShape with rightUnit | rightDiagonal
    · exact diagonal_unit_coefficients_strictly_exterior
        certificate leftDiagonal rightUnit
    · exact diagonal_diagonal_coefficients_strictly_exterior
        certificate leftDiagonal rightDiagonal

/-- Eliminate the trailing coefficient to express the leading coefficient times the critical determinant gap factor. -/
private theorem
  left_coefficient_gap_identity
    (value : Fraction.Rational) (left right : GaussianInt) :
    GaussianInt.toGaussian left *
        (1 - criticalDenominatorRatio value *
          criticalErrorRatio value) =
      (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) -
        (GaussianInt.toGaussian left * criticalDenominatorRatio value +
          GaussianInt.toGaussian right) * criticalErrorRatio value := by
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
    ring1

/-- Eliminate the leading coefficient to express the trailing coefficient times the critical determinant gap factor. -/
private theorem
  right_coefficient_gap_identity
    (value : Fraction.Rational) (left right : GaussianInt) :
    GaussianInt.toGaussian right *
        (1 - criticalDenominatorRatio value *
          criticalErrorRatio value) =
      (GaussianInt.toGaussian left * criticalDenominatorRatio value +
          GaussianInt.toGaussian right) -
        criticalDenominatorRatio value *
          (GaussianInt.toGaussian left +
            GaussianInt.toGaussian right * criticalErrorRatio value) := by
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
    ring1

/-- Coefficients of a point in the closed critical cylinder each have quadrance below four.

The two elimination identities and the explicit positive gap margin convert unit error and denominator bounds into
strict finite coefficient bounds. -/
theorem
  coefficient_normNat_lt_four_of_critical_inside
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    (left right : GaussianInt)
    (errorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * criticalErrorRatio value) ≤ 1)
    (denominatorBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) ≤ 1) :
    GaussianInt.normNat left < 4 ∧ GaussianInt.normNat right < 4 := by
  have coordinateNonnegative := criticalCoordinateNorm_nonnegative value
  have gapPositive := criticalGap_pos certificate
  have margin := twice_one_add_coordinateNorm_lt_four_gap certificate
  have denominatorScaledLe :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
          GaussianInt.toGaussian right) * criticalCoordinateNorm value ≤
        criticalCoordinateNorm value := by
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
            GaussianInt.toGaussian right) * criticalCoordinateNorm value ≤
          (1 : Fraction.Rational) * criticalCoordinateNorm value :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          denominatorBound coordinateNonnegative
      _ = criticalCoordinateNorm value := by ring1
  have errorScaledLe :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) *
          criticalCoordinateNorm value ≤
            criticalCoordinateNorm value := by
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
            GaussianInt.toGaussian right * criticalErrorRatio value) *
            criticalCoordinateNorm value ≤
          (1 : Fraction.Rational) * criticalCoordinateNorm value :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          errorBound coordinateNonnegative
      _ = criticalCoordinateNorm value := by ring1
  have leftSumBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) +
        Data.Gaussian.Norm.Basic.normSq ((GaussianInt.toGaussian left *
          criticalDenominatorRatio value +
          GaussianInt.toGaussian right) * criticalErrorRatio value) ≤
        1 + criticalCoordinateNorm value := by
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
            GaussianInt.toGaussian right * criticalErrorRatio value) +
          Data.Gaussian.Norm.Basic.normSq ((GaussianInt.toGaussian left *
            criticalDenominatorRatio value +
            GaussianInt.toGaussian right) * criticalErrorRatio value) =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * criticalErrorRatio value) +
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
              criticalDenominatorRatio value +
              GaussianInt.toGaussian right) * criticalCoordinateNorm value := by
        rw [Gaussian.Norm.Basic.normSq_mul, normSq_criticalErrorRatio]
      _ ≤ 1 + criticalCoordinateNorm value :=
        Fraction.Order.Arithmetic.add_le_add_direct
          errorBound denominatorScaledLe
  have rightSumBound :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
          GaussianInt.toGaussian right) +
        Data.Gaussian.Norm.Basic.normSq (criticalDenominatorRatio value *
          (GaussianInt.toGaussian left +
            GaussianInt.toGaussian right * criticalErrorRatio value)) ≤
        1 + criticalCoordinateNorm value := by
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
            GaussianInt.toGaussian right) +
          Data.Gaussian.Norm.Basic.normSq (criticalDenominatorRatio value *
            (GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * criticalErrorRatio value)) =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
            criticalDenominatorRatio value +
              GaussianInt.toGaussian right) +
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
                GaussianInt.toGaussian right * criticalErrorRatio value) *
              criticalCoordinateNorm value := by
        rw [Gaussian.Norm.Basic.normSq_mul, normSq_criticalDenominatorRatio]
        ring1
      _ ≤ 1 + criticalCoordinateNorm value :=
        Fraction.Order.Arithmetic.add_le_add_direct
          denominatorBound errorScaledLe
  have leftProductStrict :
      (GaussianInt.normNat left : Fraction.Rational) * criticalGap value <
        4 * criticalGap value := by
    calc
      (GaussianInt.normNat left : Fraction.Rational) * criticalGap value =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
            (1 - criticalDenominatorRatio value *
              criticalErrorRatio value)) := by
        unfold criticalGap
        rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
      _ = Data.Gaussian.Norm.Basic.normSq
          ((GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * criticalErrorRatio value) -
            (GaussianInt.toGaussian left * criticalDenominatorRatio value +
              GaussianInt.toGaussian right) * criticalErrorRatio value) := by
        rw [left_coefficient_gap_identity]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
              GaussianInt.toGaussian right * criticalErrorRatio value) +
            Data.Gaussian.Norm.Basic.normSq ((GaussianInt.toGaussian left *
              criticalDenominatorRatio value +
              GaussianInt.toGaussian right) * criticalErrorRatio value)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (1 + criticalCoordinateNorm value) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ < 4 * criticalGap value := margin
  have rightProductStrict :
      (GaussianInt.normNat right : Fraction.Rational) * criticalGap value <
        4 * criticalGap value := by
    calc
      (GaussianInt.normNat right : Fraction.Rational) * criticalGap value =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian right *
            (1 - criticalDenominatorRatio value *
              criticalErrorRatio value)) := by
        unfold criticalGap
        rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
      _ = Data.Gaussian.Norm.Basic.normSq
          ((GaussianInt.toGaussian left * criticalDenominatorRatio value +
              GaussianInt.toGaussian right) -
            criticalDenominatorRatio value *
              (GaussianInt.toGaussian left +
                GaussianInt.toGaussian right * criticalErrorRatio value)) := by
        rw [right_coefficient_gap_identity]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
            criticalDenominatorRatio value +
              GaussianInt.toGaussian right) +
            Data.Gaussian.Norm.Basic.normSq (criticalDenominatorRatio value *
              (GaussianInt.toGaussian left +
                GaussianInt.toGaussian right * criticalErrorRatio value))) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (1 + criticalCoordinateNorm value) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ < 4 * criticalGap value := margin
  refine ⟨?_, ?_⟩
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      leftProductStrict gapPositive
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      rightProductStrict gapPositive

/-- Every nonzero integral coefficient pair leaves the open normalized
critical cylinder.  This is a finite, exact minimal-cylinder certificate;
the proof first derives the bound `normNat < 4` for both coefficients and
then checks the resulting unit/diagonal cases explicitly. -/
theorem criticalCylinderExterior
    {value : Fraction.Rational} (certificate : IsCriticalParameter value)
    (left right : GaussianInt) (coefficientNonzero : left ≠ 0 ∨ right ≠ 0) :
    (1 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
          GaussianInt.toGaussian right * criticalErrorRatio value) ∨
      1 ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
        GaussianInt.toGaussian right) := by
  by_cases errorInside :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
        GaussianInt.toGaussian right * criticalErrorRatio value) < 1
  · by_cases denominatorInside :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
        criticalDenominatorRatio value +
          GaussianInt.toGaussian right) < 1
    · have small := coefficient_normNat_lt_four_of_critical_inside
        certificate left right errorInside.le denominatorInside.le
      by_cases leftZero : left = 0
      · have rightNonzero : right ≠ 0 := by
          rcases coefficientNonzero with impossible | rightNonzero
          · exact (impossible leftZero).elim
          · exact rightNonzero
        have oneLeRight : 1 ≤ GaussianInt.normNat right :=
          GaussianInt.normNat_pos rightNonzero
        have oneLeRightCast : (1 : Fraction.Rational) ≤ (GaussianInt.normNat right : Fraction.Rational) :=
          Fraction.Cast.Order.natCast_le_direct oneLeRight
        have denominatorOneLe :
            (1 : Fraction.Rational) ≤
              Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left *
                criticalDenominatorRatio value +
                GaussianInt.toGaussian right) := by
          rw [leftZero, GaussianInt.toGaussian_zero,
            Gaussian.Basic.zero_mul,
            Gaussian.Basic.zero_add, GaussianInt.normSq_toGaussian]
          exact oneLeRightCast
        exact (not_lt_of_ge denominatorOneLe denominatorInside).elim
      · by_cases rightZero : right = 0
        · have oneLeLeft : 1 ≤ GaussianInt.normNat left :=
            GaussianInt.normNat_pos leftZero
          have oneLeLeftCast :
              (1 : Fraction.Rational) ≤ (GaussianInt.normNat left : Fraction.Rational) :=
            Fraction.Cast.Order.natCast_le_direct oneLeLeft
          have errorOneLe :
              (1 : Fraction.Rational) ≤
                Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left +
                  GaussianInt.toGaussian right * criticalErrorRatio value) := by
            rw [rightZero, GaussianInt.toGaussian_zero,
              Gaussian.Basic.zero_mul,
              Gaussian.Basic.add_zero, GaussianInt.normSq_toGaussian]
            exact oneLeLeftCast
          exact (not_lt_of_ge errorOneLe errorInside).elim
        · rcases small_nonzero_coefficients_strictly_exterior
              certificate left right leftZero rightZero small.1 small.2 with
            errorExterior | denominatorExterior
          · exact (not_lt_of_ge errorInside.le errorExterior).elim
          · exact (not_lt_of_ge denominatorInside.le
              denominatorExterior).elim
    · exact Or.inr (le_of_not_gt denominatorInside)
  · exact Or.inl (le_of_not_gt errorInside)
end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic

end
