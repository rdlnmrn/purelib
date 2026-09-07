import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.IndexOneWindow

/-!
# Finite sharpness witnesses for the Dirichlet window

This module constructs a wholly rational family of index-one windows.  The
parameters satisfy the Pell identity

`m ^ 2 - 4 * m * n + n ^ 2 = 1`,

so their normalized coordinates approach the quadratic boundary without
introducing its omitted irrational zero.  Every member is finite data and
will carry its own minimal-cylinder certificate.
-/

namespace RFAP.FiniteWindowSharpness

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.BestApproximation
open RFAP.HurwitzApproximation

/-- The scalar boundary polynomial used by the critical rational family. -/
def parameterPolynomial (value : Coordinate) : Coordinate :=
  value ^ 2 - 4 * value + 1

/-- The useful open rational side of the critical parameter chamber. -/
def IsFiniteCriticalParameter (value : Coordinate) : Prop :=
  (1 / 4 : Coordinate) ≤ value ∧ value < 1 / 3 ∧
    0 < parameterPolynomial value

private def half : Coordinate := 1 / 2

private theorem two_mul_half : (2 : Coordinate) * half = 1 := by
  unfold half
  decide

private theorem half_mul_two : half * (2 : Coordinate) = 1 := by
  rw [RFAP.ConstructiveFraction.mul_comm]
  exact two_mul_half

private theorem half_sq_mul_four : half ^ 2 * (4 : Coordinate) = 1 := by
  unfold half
  decide

private theorem four_mul_half_sq : (4 : Coordinate) * half ^ 2 = 1 := by
  rw [RFAP.ConstructiveFraction.mul_comm]
  exact half_sq_mul_four

private theorem half_sq : half ^ 2 = (1 / 4 : Coordinate) := by
  unfold half
  decide

private theorem half_mul_sq (value : Coordinate) :
    (half * value) ^ 2 = (1 / 4 : Coordinate) * value ^ 2 := by
  calc
    (half * value) ^ 2 = half ^ 2 * value ^ 2 := by ring1
    _ = (1 / 4 : Coordinate) * value ^ 2 := by rw [half_sq]

/-- The normalized upper error at critical parameter `value`. -/
def criticalErrorRatio (value : Coordinate) : Gaussian :=
  ⟨half, half * value⟩

/-- The normalized lower denominator at critical parameter `value`. -/
def criticalDenominatorRatio (value : Coordinate) : Gaussian :=
  ⟨half * value, -half⟩

/-- The common quadrance of the two normalized critical coordinates. -/
def criticalCoordinateNorm (value : Coordinate) : Coordinate :=
  half ^ 2 + (half * value) ^ 2

/-- The normalized form of one quarter of the boundary polynomial. -/
def normalizedDefect (value : Coordinate) : Coordinate :=
  half ^ 2 - 2 * half * value + (half * value) ^ 2

/-- The normalized determinant gap of the critical rational family. -/
def criticalGap (value : Coordinate) : Coordinate :=
  normSq (1 - criticalDenominatorRatio value * criticalErrorRatio value)

theorem normSq_criticalErrorRatio (value : Coordinate) :
    normSq (criticalErrorRatio value) = criticalCoordinateNorm value := by
  unfold criticalErrorRatio criticalCoordinateNorm normSq
  rfl

theorem normSq_criticalDenominatorRatio (value : Coordinate) :
    normSq (criticalDenominatorRatio value) = criticalCoordinateNorm value := by
  unfold criticalDenominatorRatio criticalCoordinateNorm normSq
  change (half * value) ^ 2 + (-half) ^ 2 =
    half ^ 2 + (half * value) ^ 2
  ring1

theorem criticalGap_eq (value : Coordinate) :
    criticalGap value =
      (1 - 2 * half ^ 2 * value) ^ 2 +
        (half ^ 2 - (half * value) ^ 2) ^ 2 := by
  unfold criticalGap criticalErrorRatio criticalDenominatorRatio normSq
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.one_re,
    RFAP.ConstructiveGaussian.Gaussian.one_im]
  ring1

theorem normalizedDefect_mul_four (value : Coordinate) :
    normalizedDefect value * 4 = parameterPolynomial value := by
  calc
    normalizedDefect value * 4 =
        half ^ 2 * 4 - 4 * (2 * half) * value +
          half ^ 2 * 4 * value ^ 2 := by
      unfold normalizedDefect
      ring1
    _ = parameterPolynomial value := by
      rw [two_mul_half, half_sq_mul_four]
      unfold parameterPolynomial
      ring1

private theorem criticalParameter_nonnegative
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 ≤ value :=
  (show (0 : Coordinate) ≤ 1 / 4 by decide).trans certificate.1

private theorem criticalParameter_le_oneThird
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    value ≤ 1 / 3 := certificate.2.1.le

private theorem criticalCoordinateNorm_lt_one
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    criticalCoordinateNorm value < 1 := by
  have valueNonnegative := criticalParameter_nonnegative certificate
  have scaledBound : half * value ≤ half * (1 / 3 : Coordinate) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (criticalParameter_le_oneThird certificate)
      (show (0 : Coordinate) ≤ half by unfold half; decide)
  have squareBound : (half * value) ^ 2 ≤
      (half * (1 / 3 : Coordinate)) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (show (0 : Coordinate) ≤ half by unfold half; decide)
        valueNonnegative)
      scaledBound 2
  calc
    criticalCoordinateNorm value =
        half ^ 2 + (half * value) ^ 2 := rfl
    _ = (half * value) ^ 2 + half ^ 2 := by ring1
    _ ≤ (half * (1 / 3 : Coordinate)) ^ 2 + half ^ 2 :=
      add_le_add_left squareBound _
    _ = half ^ 2 + (half * (1 / 3 : Coordinate)) ^ 2 := by ring1
    _ < 1 := by decide

private theorem criticalCoordinateNorm_nonnegative (value : Coordinate) :
    0 ≤ criticalCoordinateNorm value := by
  unfold criticalCoordinateNorm
  exact add_nonneg
    (RFAP.ConstructiveFraction.sq_nonneg_direct half)
    (RFAP.ConstructiveFraction.sq_nonneg_direct (half * value))

private theorem criticalCoordinateNorm_pos (value : Coordinate) :
    0 < criticalCoordinateNorm value := by
  calc
    (0 : Coordinate) < half ^ 2 := by rw [half_sq]; decide
    _ ≤ half ^ 2 + (half * value) ^ 2 :=
      le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct (half * value))
    _ = criticalCoordinateNorm value := rfl

/-- The elementary coefficient estimate below has genuine slack throughout
the finite critical chamber.  This replaces a compactness or shortest-vector
argument by the displayed quartic margin `7 - 16*s + s^4`. -/
private theorem twice_one_add_coordinateNorm_lt_four_gap
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    2 * (1 + criticalCoordinateNorm value) < 4 * criticalGap value := by
  have scaledParameter : 16 * value < 16 * (1 / 3 : Coordinate) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 16 by decide) certificate.2.1
  have sixteenValueLtSeven : 16 * value < (7 : Coordinate) :=
    scaledParameter.trans (by decide)
  have linearMargin : 0 < 7 - 16 * value :=
    RFAP.ConstructiveFraction.sub_pos_direct sixteenValueLtSeven
  have quarticNonnegative : 0 ≤ value ^ 4 :=
    RFAP.ConstructiveFraction.pow_nonneg_direct
      (criticalParameter_nonnegative certificate) 4
  have quarticMargin : 0 < 7 - 16 * value + value ^ 4 :=
    linearMargin.trans_le (le_add_of_nonneg_right quarticNonnegative)
  apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Coordinate) * 4 = 0 := by ring1
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
            ring1
          _ =
              (4 * criticalGap value -
                2 * (1 + criticalCoordinateNorm value)) * 4 := by
            rw [four_mul_half_sq]
            ring1
  · decide

private theorem criticalGap_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < criticalGap value := by
  have positiveLeft :
      0 < 2 * (1 + criticalCoordinateNorm value) := by
    have onePositive :
        (0 : Coordinate) < 1 + criticalCoordinateNorm value :=
      (show (0 : Coordinate) < 1 by decide).trans_le
        (le_add_of_nonneg_right (criticalCoordinateNorm_nonnegative value))
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide) onePositive
  have positiveScaled : 0 < 4 * criticalGap value :=
    positiveLeft.trans
      (twice_one_add_coordinateNorm_lt_four_gap certificate)
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Coordinate) * 4 = 0 := by ring1
      _ < 4 * criticalGap value := positiveScaled
      _ = criticalGap value * 4 := by ring1
  · decide

private def scaledErrorReal
    (left right : GaussianInt) (value : Coordinate) : Coordinate :=
  2 * (left.re : Coordinate) + (right.re : Coordinate) -
    (right.im : Coordinate) * value

private def scaledErrorImaginary
    (left right : GaussianInt) (value : Coordinate) : Coordinate :=
  2 * (left.im : Coordinate) + (right.im : Coordinate) +
    (right.re : Coordinate) * value

private def scaledDenominatorReal
    (left right : GaussianInt) (value : Coordinate) : Coordinate :=
  (left.re : Coordinate) * value + (left.im : Coordinate) +
    2 * (right.re : Coordinate)

private def scaledDenominatorImaginary
    (left right : GaussianInt) (value : Coordinate) : Coordinate :=
  -(left.re : Coordinate) + (left.im : Coordinate) * value +
    2 * (right.im : Coordinate)

private theorem two_mul_error_real
    (left right : GaussianInt) (value : Coordinate) :
    2 * (toGaussian left +
      toGaussian right * criticalErrorRatio value).re =
        scaledErrorReal left right value := by
  simp only [criticalErrorRatio,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re, toGaussian]
  calc
    2 * ((left.re : Coordinate) +
        ((right.re : Coordinate) * half -
          (right.im : Coordinate) * (half * value))) =
      2 * (left.re : Coordinate) +
        (2 * half) * (right.re : Coordinate) -
          (2 * half) * (right.im : Coordinate) * value := by ring1
    _ = scaledErrorReal left right value := by
      rw [two_mul_half]
      unfold scaledErrorReal
      ring1

private theorem two_mul_error_imaginary
    (left right : GaussianInt) (value : Coordinate) :
    2 * (toGaussian left +
      toGaussian right * criticalErrorRatio value).im =
        scaledErrorImaginary left right value := by
  simp only [criticalErrorRatio,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im, toGaussian]
  calc
    2 * ((left.im : Coordinate) +
        ((right.re : Coordinate) * (half * value) +
          (right.im : Coordinate) * half)) =
      2 * (left.im : Coordinate) +
        (2 * half) * (right.im : Coordinate) +
          (2 * half) * (right.re : Coordinate) * value := by ring1
    _ = scaledErrorImaginary left right value := by
      rw [two_mul_half]
      unfold scaledErrorImaginary
      ring1

private theorem two_mul_denominator_real
    (left right : GaussianInt) (value : Coordinate) :
    2 * (toGaussian left * criticalDenominatorRatio value +
      toGaussian right).re = scaledDenominatorReal left right value := by
  simp only [criticalDenominatorRatio,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re, toGaussian]
  calc
    2 * (((left.re : Coordinate) * (half * value) -
        (left.im : Coordinate) * -half) + (right.re : Coordinate)) =
      (2 * half) * (left.re : Coordinate) * value +
        (2 * half) * (left.im : Coordinate) +
          2 * (right.re : Coordinate) := by ring1
    _ = scaledDenominatorReal left right value := by
      rw [two_mul_half]
      unfold scaledDenominatorReal
      ring1

private theorem two_mul_denominator_imaginary
    (left right : GaussianInt) (value : Coordinate) :
    2 * (toGaussian left * criticalDenominatorRatio value +
      toGaussian right).im =
        scaledDenominatorImaginary left right value := by
  simp only [criticalDenominatorRatio,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im, toGaussian]
  calc
    2 * (((left.re : Coordinate) * -half +
        (left.im : Coordinate) * (half * value)) +
          (right.im : Coordinate)) =
      -(2 * half) * (left.re : Coordinate) +
        (2 * half) * (left.im : Coordinate) * value +
          2 * (right.im : Coordinate) := by ring1
    _ = scaledDenominatorImaginary left right value := by
      rw [two_mul_half]
      unfold scaledDenominatorImaginary
      ring1

private theorem error_difference_mul_four
    (left right : GaussianInt) (value : Coordinate) :
    (normSq (toGaussian left +
      toGaussian right * criticalErrorRatio value) - 1) * 4 =
        scaledErrorReal left right value ^ 2 +
          scaledErrorImaginary left right value ^ 2 - 4 := by
  unfold normSq
  calc
    (((toGaussian left +
          toGaussian right * criticalErrorRatio value).re ^ 2 +
        (toGaussian left +
          toGaussian right * criticalErrorRatio value).im ^ 2) - 1) * 4 =
      (2 * (toGaussian left +
        toGaussian right * criticalErrorRatio value).re) ^ 2 +
      (2 * (toGaussian left +
        toGaussian right * criticalErrorRatio value).im) ^ 2 - 4 := by ring1
    _ = scaledErrorReal left right value ^ 2 +
        scaledErrorImaginary left right value ^ 2 - 4 := by
      rw [two_mul_error_real, two_mul_error_imaginary]

private theorem denominator_difference_mul_four
    (left right : GaussianInt) (value : Coordinate) :
    (normSq (toGaussian left * criticalDenominatorRatio value +
      toGaussian right) - 1) * 4 =
        scaledDenominatorReal left right value ^ 2 +
          scaledDenominatorImaginary left right value ^ 2 - 4 := by
  unfold normSq
  calc
    (((toGaussian left * criticalDenominatorRatio value +
          toGaussian right).re ^ 2 +
        (toGaussian left * criticalDenominatorRatio value +
          toGaussian right).im ^ 2) - 1) * 4 =
      (2 * (toGaussian left * criticalDenominatorRatio value +
        toGaussian right).re) ^ 2 +
      (2 * (toGaussian left * criticalDenominatorRatio value +
        toGaussian right).im) ^ 2 - 4 := by ring1
    _ = scaledDenominatorReal left right value ^ 2 +
        scaledDenominatorImaginary left right value ^ 2 - 4 := by
      rw [two_mul_denominator_real, two_mul_denominator_imaginary]

private theorem positive_of_mul_four_positive {value : Coordinate}
    (scaledPositive : 0 < value * 4) : 0 < value := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Coordinate) * 4 = 0 := by ring1
      _ < value * 4 := scaledPositive
  · decide

private theorem scaledPlus_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < 1 + 4 * value + value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + value ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (criticalParameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.sq_nonneg_direct value)
  exact (show (0 : Coordinate) < 1 by decide).trans_le
    (by
      calc
        (1 : Coordinate) ≤ 1 + (4 * value + value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 1 + 4 * value + value ^ 2 := by ring1)

private theorem scaledFive_pos {value : Coordinate} :
    0 < 5 + value ^ 2 :=
  (show (0 : Coordinate) < 5 by decide).trans_le
    (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct value))

private theorem scaledSixPlusFour_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < 6 + 4 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + 2 * value ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (criticalParameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct value))
  exact (show (0 : Coordinate) < 6 by decide).trans_le
    (by
      calc
        (6 : Coordinate) ≤ 6 + (4 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 4 * value + 2 * value ^ 2 := by ring1)

private theorem scaledNineMinusFour_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < 9 - 4 * value + value ^ 2 := by
  calc
    (0 : Coordinate) < 8 + parameterPolynomial value :=
      (show (0 : Coordinate) < 8 by decide).trans_le
        (le_add_of_nonneg_right certificate.2.2.le)
    _ = 9 - 4 * value + value ^ 2 := by
      unfold parameterPolynomial
      ring1

private theorem scaledFourteen_pos {value : Coordinate} :
    0 < 14 + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 2 * value ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.sq_nonneg_direct value)
  exact (show (0 : Coordinate) < 14 by decide).trans_le
    (le_add_of_nonneg_right tailNonnegative)

private theorem scaledSixMinusEight_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < 6 - 8 * value + 2 * value ^ 2 := by
  have doubledNonnegative : 0 ≤ 2 * parameterPolynomial value :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      certificate.2.2.le
  calc
    (0 : Coordinate) < 4 + 2 * parameterPolynomial value :=
      (show (0 : Coordinate) < 4 by decide).trans_le
        (le_add_of_nonneg_right doubledNonnegative)
    _ = 6 - 8 * value + 2 * value ^ 2 := by
      unfold parameterPolynomial
      ring1

private theorem scaledSixPlusEight_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < 6 + 8 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 8 * value + 2 * value ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (criticalParameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct value))
  exact (show (0 : Coordinate) < 6 by decide).trans_le
    (by
      calc
        (6 : Coordinate) ≤ 6 + (8 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 8 * value + 2 * value ^ 2 := by ring1)

private theorem scaledMinus_pos
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    0 < 1 - 4 * value + value ^ 2 := by
  calc
    (0 : Coordinate) < parameterPolynomial value := certificate.2.2
    _ = 1 - 4 * value + value ^ 2 := by
      unfold parameterPolynomial
      ring1

macro "scaled_ring" : tactic =>
  `(tactic| (simp [scaledErrorReal, scaledErrorImaginary,
      scaledDenominatorReal, scaledDenominatorImaginary, toGaussian,
      RFAP.HurwitzGeometry.imaginaryUnit] <;> ring1))

macro "solve_critical_exterior" certificate:term "," value:term : tactic =>
  `(tactic| first
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledMinus_pos $certificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledMinus_pos $certificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledPlus_pos $certificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledPlus_pos $certificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledFive_pos (value := $value) using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledFive_pos (value := $value) using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledSixPlusFour_pos $certificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledSixPlusFour_pos $certificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledNineMinusFour_pos $certificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledNineMinusFour_pos $certificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledFourteen_pos (value := $value) using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledFourteen_pos (value := $value) using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledSixMinusEight_pos $certificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledSixMinusEight_pos $certificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert scaledSixPlusEight_pos $certificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert scaledSixPlusEight_pos $certificate using 1 <;> scaled_ring)

private theorem unit_unit_coefficients_strictly_exterior
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    {left right : GaussianInt}
    (leftUnit : RFAP.HurwitzGeometry.IsGaussianUnit left)
    (rightUnit : RFAP.HurwitzGeometry.IsGaussianUnit right) :
    (1 : Coordinate) <
        normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) ∨
      1 < normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl <;>
    rcases rightUnit with rfl | rfl | rfl | rfl <;>
      solve_critical_exterior certificate, value

private theorem unit_diagonal_coefficients_strictly_exterior
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    {left right : GaussianInt}
    (leftUnit : RFAP.HurwitzGeometry.IsGaussianUnit left)
    (rightDiagonal : RFAP.HurwitzGeometry.IsDiagonal right) :
    (1 : Coordinate) <
        normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) ∨
      1 < normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl <;>
    rcases rightDiagonal with rfl | rfl | rfl | rfl <;>
      solve_critical_exterior certificate, value

private theorem diagonal_unit_coefficients_strictly_exterior
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    {left right : GaussianInt}
    (leftDiagonal : RFAP.HurwitzGeometry.IsDiagonal left)
    (rightUnit : RFAP.HurwitzGeometry.IsGaussianUnit right) :
    (1 : Coordinate) <
        normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) ∨
      1 < normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
    rcases rightUnit with rfl | rfl | rfl | rfl <;>
      solve_critical_exterior certificate, value

private theorem diagonal_diagonal_coefficients_strictly_exterior
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    {left right : GaussianInt}
    (leftDiagonal : RFAP.HurwitzGeometry.IsDiagonal left)
    (rightDiagonal : RFAP.HurwitzGeometry.IsDiagonal right) :
    (1 : Coordinate) <
        normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) ∨
      1 < normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
    rcases rightDiagonal with rfl | rfl | rfl | rfl <;>
      solve_critical_exterior certificate, value

private theorem small_nonzero_coefficients_strictly_exterior
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    (left right : GaussianInt)
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0)
    (leftSmall : normNat left < 4) (rightSmall : normNat right < 4) :
    (1 : Coordinate) <
        normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) ∨
      1 < normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) := by
  have leftShape :
      RFAP.HurwitzGeometry.IsGaussianUnit left ∨
        RFAP.HurwitzGeometry.IsDiagonal left := by
    rcases RFAP.HurwitzGeometry.normNat_eq_zero_or_one_or_two_of_lt_four
        left leftSmall with zeroNorm | unitNorm | diagonalNorm
    · exact (leftNonzero
        (RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero zeroNorm)).elim
    · exact Or.inl
        (RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one unitNorm)
    · exact Or.inr
        (RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two diagonalNorm)
  have rightShape :
      RFAP.HurwitzGeometry.IsGaussianUnit right ∨
        RFAP.HurwitzGeometry.IsDiagonal right := by
    rcases RFAP.HurwitzGeometry.normNat_eq_zero_or_one_or_two_of_lt_four
        right rightSmall with zeroNorm | unitNorm | diagonalNorm
    · exact (rightNonzero
        (RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero zeroNorm)).elim
    · exact Or.inl
        (RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one unitNorm)
    · exact Or.inr
        (RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two diagonalNorm)
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

private theorem left_coefficient_gap_identity
    (value : Coordinate) (left right : GaussianInt) :
    toGaussian left *
        (1 - criticalDenominatorRatio value * criticalErrorRatio value) =
      (toGaussian left +
          toGaussian right * criticalErrorRatio value) -
        (toGaussian left * criticalDenominatorRatio value +
          toGaussian right) * criticalErrorRatio value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
    ring1

private theorem right_coefficient_gap_identity
    (value : Coordinate) (left right : GaussianInt) :
    toGaussian right *
        (1 - criticalDenominatorRatio value * criticalErrorRatio value) =
      (toGaussian left * criticalDenominatorRatio value +
          toGaussian right) -
        criticalDenominatorRatio value *
          (toGaussian left +
            toGaussian right * criticalErrorRatio value) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
    ring1

private theorem coefficient_normNat_lt_four_of_critical_inside
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    (left right : GaussianInt)
    (errorBound :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) ≤ 1)
    (denominatorBound :
      normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) ≤ 1) :
    normNat left < 4 ∧ normNat right < 4 := by
  have coordinateNonnegative := criticalCoordinateNorm_nonnegative value
  have gapPositive := criticalGap_pos certificate
  have margin := twice_one_add_coordinateNorm_lt_four_gap certificate
  have denominatorScaledLe :
      normSq (toGaussian left * criticalDenominatorRatio value +
          toGaussian right) * criticalCoordinateNorm value ≤
        criticalCoordinateNorm value := by
    calc
      normSq (toGaussian left * criticalDenominatorRatio value +
            toGaussian right) * criticalCoordinateNorm value ≤
          (1 : Coordinate) * criticalCoordinateNorm value :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          denominatorBound coordinateNonnegative
      _ = criticalCoordinateNorm value := by ring1
  have errorScaledLe :
      normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) *
          criticalCoordinateNorm value ≤ criticalCoordinateNorm value := by
    calc
      normSq (toGaussian left +
            toGaussian right * criticalErrorRatio value) *
            criticalCoordinateNorm value ≤
          (1 : Coordinate) * criticalCoordinateNorm value :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          errorBound coordinateNonnegative
      _ = criticalCoordinateNorm value := by ring1
  have leftSumBound :
      normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) +
        normSq ((toGaussian left * criticalDenominatorRatio value +
          toGaussian right) * criticalErrorRatio value) ≤
        1 + criticalCoordinateNorm value := by
    calc
      normSq (toGaussian left +
            toGaussian right * criticalErrorRatio value) +
          normSq ((toGaussian left * criticalDenominatorRatio value +
            toGaussian right) * criticalErrorRatio value) =
          normSq (toGaussian left +
              toGaussian right * criticalErrorRatio value) +
            normSq (toGaussian left * criticalDenominatorRatio value +
              toGaussian right) * criticalCoordinateNorm value := by
        rw [normSq_mul, normSq_criticalErrorRatio]
      _ ≤ 1 + criticalCoordinateNorm value :=
        RFAP.ConstructiveFraction.add_le_add_direct
          errorBound denominatorScaledLe
  have rightSumBound :
      normSq (toGaussian left * criticalDenominatorRatio value +
          toGaussian right) +
        normSq (criticalDenominatorRatio value *
          (toGaussian left +
            toGaussian right * criticalErrorRatio value)) ≤
        1 + criticalCoordinateNorm value := by
    calc
      normSq (toGaussian left * criticalDenominatorRatio value +
            toGaussian right) +
          normSq (criticalDenominatorRatio value *
            (toGaussian left +
              toGaussian right * criticalErrorRatio value)) =
          normSq (toGaussian left * criticalDenominatorRatio value +
              toGaussian right) +
            normSq (toGaussian left +
                toGaussian right * criticalErrorRatio value) *
              criticalCoordinateNorm value := by
        rw [normSq_mul, normSq_criticalDenominatorRatio]
        ring1
      _ ≤ 1 + criticalCoordinateNorm value :=
        RFAP.ConstructiveFraction.add_le_add_direct
          denominatorBound errorScaledLe
  have leftProductStrict :
      (normNat left : Coordinate) * criticalGap value <
        4 * criticalGap value := by
    calc
      (normNat left : Coordinate) * criticalGap value =
          normSq (toGaussian left *
            (1 - criticalDenominatorRatio value *
              criticalErrorRatio value)) := by
        unfold criticalGap
        rw [normSq_mul, normSq_toGaussian]
      _ = normSq
          ((toGaussian left +
              toGaussian right * criticalErrorRatio value) -
            (toGaussian left * criticalDenominatorRatio value +
              toGaussian right) * criticalErrorRatio value) := by
        rw [left_coefficient_gap_identity]
      _ ≤ 2 *
          (normSq (toGaussian left +
              toGaussian right * criticalErrorRatio value) +
            normSq ((toGaussian left * criticalDenominatorRatio value +
              toGaussian right) * criticalErrorRatio value)) :=
        normSq_sub_le_two _ _
      _ ≤ 2 * (1 + criticalCoordinateNorm value) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ < 4 * criticalGap value := margin
  have rightProductStrict :
      (normNat right : Coordinate) * criticalGap value <
        4 * criticalGap value := by
    calc
      (normNat right : Coordinate) * criticalGap value =
          normSq (toGaussian right *
            (1 - criticalDenominatorRatio value *
              criticalErrorRatio value)) := by
        unfold criticalGap
        rw [normSq_mul, normSq_toGaussian]
      _ = normSq
          ((toGaussian left * criticalDenominatorRatio value +
              toGaussian right) -
            criticalDenominatorRatio value *
              (toGaussian left +
                toGaussian right * criticalErrorRatio value)) := by
        rw [right_coefficient_gap_identity]
      _ ≤ 2 *
          (normSq (toGaussian left * criticalDenominatorRatio value +
              toGaussian right) +
            normSq (criticalDenominatorRatio value *
              (toGaussian left +
                toGaussian right * criticalErrorRatio value))) :=
        normSq_sub_le_two _ _
      _ ≤ 2 * (1 + criticalCoordinateNorm value) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ < 4 * criticalGap value := margin
  refine ⟨?_, ?_⟩
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      leftProductStrict gapPositive
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      rightProductStrict gapPositive

/-- Every nonzero integral coefficient pair leaves the open normalized
critical cylinder.  This is a finite, exact minimal-cylinder certificate;
the proof first derives the bound `normNat < 4` for both coefficients and
then checks the resulting unit/diagonal cases explicitly. -/
theorem criticalCylinderExterior
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    (left right : GaussianInt) (coefficientNonzero : left ≠ 0 ∨ right ≠ 0) :
    (1 : Coordinate) ≤
        normSq (toGaussian left +
          toGaussian right * criticalErrorRatio value) ∨
      1 ≤ normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) := by
  by_cases errorInside :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) < 1
  · by_cases denominatorInside :
      normSq (toGaussian left * criticalDenominatorRatio value +
          toGaussian right) < 1
    · have small := coefficient_normNat_lt_four_of_critical_inside
        certificate left right errorInside.le denominatorInside.le
      by_cases leftZero : left = 0
      · have rightNonzero : right ≠ 0 := by
          rcases coefficientNonzero with impossible | rightNonzero
          · exact (impossible leftZero).elim
          · exact rightNonzero
        have oneLeRight : 1 ≤ normNat right :=
          RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos rightNonzero
        have oneLeRightCast : (1 : Coordinate) ≤ (normNat right : Coordinate) :=
          RFAP.ConstructiveFraction.natCast_le_direct oneLeRight
        have denominatorOneLe :
            (1 : Coordinate) ≤
              normSq (toGaussian left * criticalDenominatorRatio value +
                toGaussian right) := by
          rw [leftZero, toGaussian_zero,
            RFAP.ConstructiveGaussian.Gaussian.zero_mul,
            RFAP.ConstructiveGaussian.Gaussian.zero_add, normSq_toGaussian]
          exact oneLeRightCast
        exact (not_lt_of_ge denominatorOneLe denominatorInside).elim
      · by_cases rightZero : right = 0
        · have oneLeLeft : 1 ≤ normNat left :=
            RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos leftZero
          have oneLeLeftCast :
              (1 : Coordinate) ≤ (normNat left : Coordinate) :=
            RFAP.ConstructiveFraction.natCast_le_direct oneLeLeft
          have errorOneLe :
              (1 : Coordinate) ≤
                normSq (toGaussian left +
                  toGaussian right * criticalErrorRatio value) := by
            rw [rightZero, toGaussian_zero,
              RFAP.ConstructiveGaussian.Gaussian.zero_mul,
              RFAP.ConstructiveGaussian.Gaussian.add_zero, normSq_toGaussian]
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

/-! ## An unbounded displayed Pell family -/

/-- The additive Pell state `(m,d)`, with the eventual denominator
`n=m+d`.  Keeping the positive difference `d` rather than a signed matrix
recurrence makes every executable step subtraction-free. -/
def pellState : Nat → Nat × Nat
  | 0 => (1, 3)
  | stage + 1 =>
      let previous := pellState stage
      (previous.1 + previous.2, 2 * previous.1 + 3 * previous.2)

/-- Numerator `m` of the critical rational parameter. -/
def pellNumerator (stage : Nat) : Nat := (pellState stage).1

/-- Positive difference `d=n-m` in the subtraction-free recurrence. -/
def pellDifference (stage : Nat) : Nat := (pellState stage).2

/-- Denominator `n=m+d` of the critical rational parameter. -/
def pellDenominator (stage : Nat) : Nat :=
  pellNumerator stage + pellDifference stage

@[simp] theorem pellNumerator_zero : pellNumerator 0 = 1 := rfl
@[simp] theorem pellDifference_zero : pellDifference 0 = 3 := rfl
@[simp] theorem pellDenominator_zero : pellDenominator 0 = 4 := rfl

@[simp] theorem pellNumerator_succ (stage : Nat) :
    pellNumerator (stage + 1) =
      pellNumerator stage + pellDifference stage := by
  rfl

@[simp] theorem pellDifference_succ (stage : Nat) :
    pellDifference (stage + 1) =
      2 * pellNumerator stage + 3 * pellDifference stage := by
  rfl

/-- The subtraction-free form of the Pell identity. -/
theorem pellDifference_sq
    (stage : Nat) :
    pellDifference stage ^ 2 =
      2 * pellNumerator stage ^ 2 +
        2 * pellNumerator stage * pellDifference stage + 1 := by
  induction stage with
  | zero => decide
  | succ stage inductionHypothesis =>
      rw [pellNumerator_succ, pellDifference_succ]
      apply Nat.add_left_cancel
      calc
        (2 * pellNumerator stage ^ 2 +
              2 * pellNumerator stage * pellDifference stage) +
            (2 * pellNumerator stage +
              3 * pellDifference stage) ^ 2 =
          (2 * (pellNumerator stage + pellDifference stage) ^ 2 +
              2 * (pellNumerator stage + pellDifference stage) *
                (2 * pellNumerator stage + 3 * pellDifference stage)) +
            pellDifference stage ^ 2 := by ring1
        _ =
          (2 * (pellNumerator stage + pellDifference stage) ^ 2 +
              2 * (pellNumerator stage + pellDifference stage) *
                (2 * pellNumerator stage + 3 * pellDifference stage)) +
            (2 * pellNumerator stage ^ 2 +
              2 * pellNumerator stage * pellDifference stage + 1) := by
          rw [inductionHypothesis]
        _ =
          (2 * pellNumerator stage ^ 2 +
              2 * pellNumerator stage * pellDifference stage) +
            (2 * (pellNumerator stage + pellDifference stage) ^ 2 +
              2 * (pellNumerator stage + pellDifference stage) *
                (2 * pellNumerator stage + 3 * pellDifference stage) + 1) := by
          ring1

/-- The positive state remains in the elementary chamber
`2*m < d ≤ 3*m`. -/
theorem pellDifference_bounds (stage : Nat) :
    2 * pellNumerator stage < pellDifference stage ∧
      pellDifference stage ≤ 3 * pellNumerator stage := by
  induction stage with
  | zero => decide
  | succ stage inductionHypothesis =>
      rw [pellNumerator_succ, pellDifference_succ]
      have differencePositive : 0 < pellDifference stage :=
        (Nat.zero_le (2 * pellNumerator stage)).trans_lt
          inductionHypothesis.1
      constructor
      · calc
          2 * (pellNumerator stage + pellDifference stage) =
              2 * pellNumerator stage + 2 * pellDifference stage := by ring1
          _ < 2 * pellNumerator stage + 3 * pellDifference stage :=
            Nat.add_lt_add_left
              (Nat.mul_lt_mul_of_pos_right (by decide) differencePositive) _
      · calc
          2 * pellNumerator stage + 3 * pellDifference stage ≤
              3 * pellNumerator stage + 3 * pellDifference stage :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_right (pellNumerator stage) (by decide)) _
          _ = 3 * (pellNumerator stage + pellDifference stage) := by ring1

theorem pellNumerator_pos (stage : Nat) : 0 < pellNumerator stage := by
  induction stage with
  | zero => decide
  | succ stage inductionHypothesis =>
      rw [pellNumerator_succ]
      exact inductionHypothesis.trans_le
        (Nat.le_add_right (pellNumerator stage) (pellDifference stage))

theorem pellDifference_pos (stage : Nat) : 0 < pellDifference stage := by
  exact (Nat.zero_le (2 * pellNumerator stage)).trans_lt
    (pellDifference_bounds stage).1

theorem pellDenominator_pos (stage : Nat) : 0 < pellDenominator stage := by
  unfold pellDenominator
  exact (pellNumerator_pos stage).trans_le
    (Nat.le_add_right (pellNumerator stage) (pellDifference stage))

/-- Squaring preserves a strict natural-number comparison.  The direct
finite proof avoids the generic upstream order lemma's quotient-bearing
inheritance route. -/
theorem natMulSelf_lt_natMulSelf {left right : Nat}
    (less : left < right) : left * left < right * right := by
  cases left with
  | zero =>
      simpa only [Nat.zero_mul] using
        Nat.mul_pos (Nat.zero_lt_of_lt less) (Nat.zero_lt_of_lt less)
  | succ left =>
      exact
        (Nat.mul_lt_mul_of_pos_left less (Nat.succ_pos left)).trans
          (Nat.mul_lt_mul_of_pos_right less (Nat.zero_lt_of_lt less))

/-- Denominators in the displayed family exceed the recursion index, giving
a direct finite witness above every supplied natural scale. -/
theorem stage_lt_pellDenominator (stage : Nat) :
    stage < pellDenominator stage := by
  have numeratorGrowth : stage < pellNumerator stage := by
    induction stage with
    | zero => decide
    | succ stage inductionHypothesis =>
        rw [pellNumerator_succ]
        have differencePositive := pellDifference_pos stage
        exact (Nat.succ_le_of_lt inductionHypothesis).trans_lt (by
          simpa only [Nat.add_zero] using
            Nat.add_lt_add_left differencePositive (pellNumerator stage))
  unfold pellDenominator
  exact numeratorGrowth.trans_le
    (Nat.le_add_right (pellNumerator stage) (pellDifference stage))

/-- The usual Pell equation, written without natural subtraction. -/
theorem pellEquation (stage : Nat) :
    pellNumerator stage ^ 2 + pellDenominator stage ^ 2 =
      4 * pellNumerator stage * pellDenominator stage + 1 := by
  calc
    pellNumerator stage ^ 2 + pellDenominator stage ^ 2 =
        2 * pellNumerator stage ^ 2 +
          2 * pellNumerator stage * pellDifference stage +
            pellDifference stage ^ 2 := by
      unfold pellDenominator
      ring1
    _ = 4 * pellNumerator stage ^ 2 +
        4 * pellNumerator stage * pellDifference stage + 1 := by
      rw [pellDifference_sq]
      ring1
    _ = 4 * pellNumerator stage * pellDenominator stage + 1 := by
      unfold pellDenominator
      ring1

/-- The rational critical parameter `m/n` at a supplied finite stage. -/
def pellParameter (stage : Nat) : Coordinate :=
  (pellNumerator stage : Coordinate) / (pellDenominator stage : Coordinate)

private theorem pellDenominator_cast_pos (stage : Nat) :
    (0 : Coordinate) < (pellDenominator stage : Coordinate) :=
  RFAP.ConstructiveFraction.natCast_pos_direct (pellDenominator_pos stage)

/-- Clearing the explicitly positive Pell denominator recovers its numerator. -/
theorem pellParameter_mul_denominator (stage : Nat) :
    pellParameter stage * (pellDenominator stage : Coordinate) =
      (pellNumerator stage : Coordinate) := by
  unfold pellParameter
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
    (pellDenominator_cast_pos stage).ne'

/-- The parameter polynomial is strictly positive at every finite Pell
stage; after clearing the displayed denominator its value is exactly one. -/
theorem parameterPolynomial_pellParameter_scaled (stage : Nat) :
    parameterPolynomial (pellParameter stage) *
        (pellDenominator stage : Coordinate) ^ 2 = 1 := by
  have castEquation := congrArg (fun value : Nat => (value : Coordinate))
    (pellEquation stage)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    at castEquation
  calc
    parameterPolynomial (pellParameter stage) *
          (pellDenominator stage : Coordinate) ^ 2 =
        (pellParameter stage * (pellDenominator stage : Coordinate)) ^ 2 -
          4 * (pellParameter stage *
            (pellDenominator stage : Coordinate)) *
              (pellDenominator stage : Coordinate) +
          (pellDenominator stage : Coordinate) ^ 2 := by
      unfold parameterPolynomial
      ring1
    _ =
        (pellNumerator stage : Coordinate) ^ 2 -
          4 * (pellNumerator stage : Coordinate) *
            (pellDenominator stage : Coordinate) +
          (pellDenominator stage : Coordinate) ^ 2 := by
      rw [pellParameter_mul_denominator]
    _ = 1 := by
      calc
        (pellNumerator stage : Coordinate) ^ 2 -
              4 * (pellNumerator stage : Coordinate) *
                (pellDenominator stage : Coordinate) +
              (pellDenominator stage : Coordinate) ^ 2 =
            ((pellNumerator stage : Coordinate) ^ 2 +
                (pellDenominator stage : Coordinate) ^ 2) -
              4 * (pellNumerator stage : Coordinate) *
                (pellDenominator stage : Coordinate) := by ring1
        _ = 1 := by rw [castEquation]; ring1

theorem parameterPolynomial_pellParameter_pos (stage : Nat) :
    0 < parameterPolynomial (pellParameter stage) := by
  have denominatorSquareNonnegative :
      (0 : Coordinate) ≤ (pellDenominator stage : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have productPositive :
      0 < (pellDenominator stage : Coordinate) ^ 2 *
        parameterPolynomial (pellParameter stage) := by
    calc
      (0 : Coordinate) < 1 := by decide
      _ = (pellDenominator stage : Coordinate) ^ 2 *
          parameterPolynomial (pellParameter stage) := by
        rw [RFAP.ConstructiveFraction.mul_comm,
          parameterPolynomial_pellParameter_scaled]
  exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
    productPositive denominatorSquareNonnegative

/-- The Pell denominator is at most four times its numerator. -/
theorem pellDenominator_le_four_mul_numerator (stage : Nat) :
    pellDenominator stage ≤ 4 * pellNumerator stage := by
  unfold pellDenominator
  calc
    pellNumerator stage + pellDifference stage ≤
        pellNumerator stage + 3 * pellNumerator stage :=
      Nat.add_le_add_left (pellDifference_bounds stage).2 _
    _ = 4 * pellNumerator stage := by ring1

/-- Three times the Pell numerator is strictly below its denominator. -/
theorem three_mul_numerator_lt_pellDenominator (stage : Nat) :
    3 * pellNumerator stage < pellDenominator stage := by
  unfold pellDenominator
  calc
    3 * pellNumerator stage =
        pellNumerator stage + 2 * pellNumerator stage := by ring1
    _ < pellNumerator stage + pellDifference stage :=
      Nat.add_lt_add_left (pellDifference_bounds stage).1 _

/-- The displayed Pell parameter is at least one quarter. -/
theorem oneFourth_le_pellParameter (stage : Nat) :
    (1 / 4 : Coordinate) ≤ pellParameter stage := by
  have denominatorPositive := pellDenominator_cast_pos stage
  have castDenominatorUpper :
      (pellDenominator stage : Coordinate) ≤
        (4 * pellNumerator stage : Nat) :=
    RFAP.ConstructiveFraction.natCast_le_direct
      (pellDenominator_le_four_mul_numerator stage)
  apply (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).2
  rw [show (1 / 4 : Coordinate) *
      (pellDenominator stage : Coordinate) =
        (pellDenominator stage : Coordinate) / 4 by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.one_mul]
    exact RFAP.ConstructiveFraction.mul_comm _ _]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos (by decide)).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat,
    RFAP.ConstructiveFraction.mul_comm] using castDenominatorUpper

/-- The displayed Pell parameter is strictly below one third. -/
theorem pellParameter_lt_oneThird (stage : Nat) :
    pellParameter stage < (1 / 3 : Coordinate) := by
  have denominatorPositive := pellDenominator_cast_pos stage
  have castTripleLower :
      (3 * pellNumerator stage : Nat) <
        (pellDenominator stage : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct
      (three_mul_numerator_lt_pellDenominator stage)
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
  rw [show (1 / 3 : Coordinate) *
      (pellDenominator stage : Coordinate) =
        (pellDenominator stage : Coordinate) / 3 by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.one_mul]
    exact RFAP.ConstructiveFraction.mul_comm _ _]
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos (by decide)).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat,
    RFAP.ConstructiveFraction.mul_comm] using castTripleLower

/-- Every finite Pell ratio lies in the exact chamber required by the
minimal-cylinder calculation. -/
theorem pellParameter_isFiniteCritical (stage : Nat) :
    IsFiniteCriticalParameter (pellParameter stage) :=
  ⟨oneFourth_le_pellParameter stage, pellParameter_lt_oneThird stage,
    parameterPolynomial_pellParameter_pos stage⟩

/-! ## Concrete Gaussian pairs and their displayed source -/

/-- Lower coefficient pair for the stage-`k` critical window. -/
def criticalLowerPair (stage : Nat) : Pair :=
  { numerator :=
      ⟨-2 * (pellNumerator stage : Int), 0⟩
    denominator :=
      ⟨(pellNumerator stage : Int),
        -(pellDenominator stage : Int)⟩ }

/-- Upper coefficient pair for the stage-`k` critical window. -/
def criticalUpperPair (stage : Nat) : Pair :=
  { numerator :=
      ⟨-(pellNumerator stage : Int),
        -(pellDenominator stage : Int)⟩
    denominator :=
      ⟨2 * (pellDenominator stage : Int), 0⟩ }

theorem criticalPair_determinant (stage : Nat) :
    coefficientDeterminant (criticalLowerPair stage)
      (criticalUpperPair stage) = 1 := by
  have castEquation := congrArg (fun value : Nat => (value : Int))
    (pellEquation stage)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    at castEquation
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
  · simp only [coefficientDeterminant, determinant, criticalLowerPair,
      criticalUpperPair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re]
    calc
      (-2 * (pellNumerator stage : Int)) *
              (2 * (pellDenominator stage : Int)) - 0 * 0 -
            (-(pellNumerator stage : Int) *
                (pellNumerator stage : Int) -
              -(pellDenominator stage : Int) *
                -(pellDenominator stage : Int)) =
          (pellNumerator stage : Int) ^ 2 +
              (pellDenominator stage : Int) ^ 2 -
            4 * (pellNumerator stage : Int) *
              (pellDenominator stage : Int) := by ring1
      _ = 1 := by rw [castEquation]; ring1
  · simp only [coefficientDeterminant, determinant, criticalLowerPair,
      criticalUpperPair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im]
    ring1

theorem criticalPair_indexOne (stage : Nat) :
    coefficientIndexQuadrance (criticalLowerPair stage)
      (criticalUpperPair stage) = 1 := by
  unfold coefficientIndexQuadrance
  rw [criticalPair_determinant]
  rfl

theorem criticalLower_denominatorQuadrance (stage : Nat) :
    denominatorQuadrance (criticalLowerPair stage) =
      pellNumerator stage ^ 2 + pellDenominator stage ^ 2 := by
  unfold denominatorQuadrance criticalLowerPair
  rw [normNat_eq_component_squares]
  simp only [Int.natAbs_natCast, Int.natAbs_neg, pow_two]

theorem criticalUpper_denominatorQuadrance (stage : Nat) :
    denominatorQuadrance (criticalUpperPair stage) =
      4 * pellDenominator stage ^ 2 := by
  unfold denominatorQuadrance criticalUpperPair
  rw [normNat_eq_component_squares]
  simp only [Int.natAbs_mul, Int.natAbs_natCast,
    Int.natAbs_zero, pow_two]
  ring1

theorem criticalLower_denominator_ne_zero (stage : Nat) :
    (criticalLowerPair stage).denominator ≠ 0 := by
  intro zero
  have imaginaryZero := congrArg
    RFAP.ConstructiveGaussianHeight.GaussianInt.im zero
  simp only [criticalLowerPair,
    RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im] at imaginaryZero
  have denominatorZero : pellDenominator stage = 0 := by
    have castZero : (pellDenominator stage : Int) = 0 :=
      neg_eq_zero.mp imaginaryZero
    exact Int.ofNat_eq_zero.mp castZero
  exact (Nat.ne_of_gt (pellDenominator_pos stage)) denominatorZero

theorem criticalUpper_denominator_ne_zero (stage : Nat) :
    (criticalUpperPair stage).denominator ≠ 0 := by
  intro zero
  have realZero := congrArg
    RFAP.ConstructiveGaussianHeight.GaussianInt.re zero
  simp only [criticalUpperPair,
    RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re] at realZero
  have doubledPositive : 0 < 2 * pellDenominator stage :=
    Nat.mul_pos (by decide) (pellDenominator_pos stage)
  exact (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt doubledPositive)) realZero

theorem critical_denominatorQuadrance_ordered (stage : Nat) :
    denominatorQuadrance (criticalLowerPair stage) <
      denominatorQuadrance (criticalUpperPair stage) := by
  rw [criticalLower_denominatorQuadrance,
    criticalUpper_denominatorQuadrance]
  have numeratorLtDenominator :
      pellNumerator stage < pellDenominator stage := by
    unfold pellDenominator
    simpa only [Nat.add_zero] using
      Nat.add_lt_add_left (pellDifference_pos stage) (pellNumerator stage)
  have squareStrict : pellNumerator stage ^ 2 <
      pellDenominator stage ^ 2 := by
    simpa only [pow_two] using
      natMulSelf_lt_natMulSelf numeratorLtDenominator
  have denominatorSquarePositive : 0 < pellDenominator stage ^ 2 :=
    by
      simpa only [pow_two] using
        Nat.mul_pos (pellDenominator_pos stage) (pellDenominator_pos stage)
  calc
    pellNumerator stage ^ 2 + pellDenominator stage ^ 2 <
        pellDenominator stage ^ 2 + pellDenominator stage ^ 2 :=
      Nat.add_lt_add_right squareStrict _
    _ = 2 * pellDenominator stage ^ 2 := by ring1
    _ < 4 * pellDenominator stage ^ 2 :=
      Nat.mul_lt_mul_of_pos_right (by decide) denominatorSquarePositive

private theorem criticalLower_denominatorGaussian_ne_zero (stage : Nat) :
    toGaussian (criticalLowerPair stage).denominator ≠ 0 := by
  intro zero
  exact criticalLower_denominator_ne_zero stage (toGaussian_eq_zero.mp zero)

private theorem criticalUpper_denominatorGaussian_ne_zero (stage : Nat) :
    toGaussian (criticalUpperPair stage).denominator ≠ 0 := by
  intro zero
  exact criticalUpper_denominator_ne_zero stage (toGaussian_eq_zero.mp zero)

private theorem criticalDenominatorRatio_mul_upper (stage : Nat) :
    criticalDenominatorRatio (pellParameter stage) *
        toGaussian (criticalUpperPair stage).denominator =
      toGaussian (criticalLowerPair stage).denominator := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [criticalDenominatorRatio, criticalUpperPair,
      criticalLowerPair, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      QuotientFreeRing.intCast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero,
      Int.cast_neg]
    calc
      half * pellParameter stage *
            (2 * (pellDenominator stage : Coordinate)) - -half * 0 =
          (2 * half) *
            (pellParameter stage * (pellDenominator stage : Coordinate)) := by
        ring1
      _ = (pellNumerator stage : Coordinate) := by
        rw [two_mul_half, pellParameter_mul_denominator]
        ring1
  · simp only [criticalDenominatorRatio, criticalUpperPair,
      criticalLowerPair, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      QuotientFreeRing.intCast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero,
      Int.cast_neg]
    calc
      half * pellParameter stage * 0 +
            -half * (2 * (pellDenominator stage : Coordinate)) =
          -(2 * half) * (pellDenominator stage : Coordinate) := by ring1
      _ = -(pellDenominator stage : Coordinate) := by
        rw [two_mul_half]
        ring1

/-- The concrete pair denominators have exactly the prescribed normalized
critical ratio. -/
theorem criticalPair_denominatorRatio (stage : Nat) :
    RFAP.DirichletWindow.denominatorRatio
        (criticalLowerPair stage) (criticalUpperPair stage) =
      criticalDenominatorRatio (pellParameter stage) := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    (criticalUpper_denominatorGaussian_ne_zero stage)
  calc
    RFAP.DirichletWindow.denominatorRatio
          (criticalLowerPair stage) (criticalUpperPair stage) *
        toGaussian (criticalUpperPair stage).denominator =
      toGaussian (criticalLowerPair stage).denominator := by
        unfold RFAP.DirichletWindow.denominatorRatio
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
          RFAP.ConstructiveGaussian.Gaussian.inv_mul _
            (criticalUpper_denominatorGaussian_ne_zero stage),
          RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = criticalDenominatorRatio (pellParameter stage) *
        toGaussian (criticalUpperPair stage).denominator :=
      (criticalDenominatorRatio_mul_upper stage).symm

/-- The displayed normalized determinant factor. -/
def criticalGapVector (value : Coordinate) : Gaussian :=
  1 - criticalDenominatorRatio value * criticalErrorRatio value

@[simp] theorem normSq_criticalGapVector (value : Coordinate) :
    normSq (criticalGapVector value) = criticalGap value := rfl

private theorem criticalGapVector_ne_zero
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    criticalGapVector value ≠ 0 := by
  intro zero
  have normZero := congrArg normSq zero
  rw [normSq_criticalGapVector, normSq_zero] at normZero
  exact (ne_of_gt (criticalGap_pos certificate)) normZero

/-- The lower error is chosen by one displayed inverse so that the basis
determinant identity is exactly one. -/
def criticalLowerError (stage : Nat) : Gaussian :=
  -RFAP.ConstructiveGaussian.Gaussian.inv
    (toGaussian (criticalUpperPair stage).denominator *
      criticalGapVector (pellParameter stage))

/-- Exact Gaussian-rational source determined by the lower pair and its
displayed nonzero error. -/
def criticalSourceValue (stage : Nat) : Gaussian :=
  (toGaussian (criticalLowerPair stage).numerator +
      criticalLowerError stage) *
    RFAP.ConstructiveGaussian.Gaussian.inv
      (toGaussian (criticalLowerPair stage).denominator)

/-- Executable common-denominator presentation of the critical source. -/
def criticalSource (stage : Nat) : RFAP.HurwitzRational.Fraction :=
  let common :=
    RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian
      (criticalSourceValue stage)
  { numerator := common.numerator
    denominator := ofNat common.denominator
    denominatorNonzero := by
      intro zero
      have realZero := congrArg
        RFAP.ConstructiveGaussianHeight.GaussianInt.re zero
      exact (Nat.ne_of_gt common.denominatorPositive)
        (Int.ofNat.inj realZero) }

@[simp] theorem criticalSource_value (stage : Nat) :
    (criticalSource stage).value = criticalSourceValue stage := by
  let common :=
    RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian
      (criticalSourceValue stage)
  have denominatorNonzero :
      toGaussian (ofNat common.denominator) ≠ 0 := by
    intro zero
    have integralZero := toGaussian_eq_zero.mp zero
    have realZero := congrArg
      RFAP.ConstructiveGaussianHeight.GaussianInt.re integralZero
    exact (Nat.ne_of_gt common.denominatorPositive)
      (Int.ofNat.inj realZero)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (criticalSource stage).value * toGaussian (ofNat common.denominator) =
        toGaussian common.numerator := by
      exact RFAP.HurwitzRational.Fraction.value_mul_denominator
        (criticalSource stage)
    _ = common.value * toGaussian (ofNat common.denominator) :=
      common.value_mul_denominator.symm
    _ = criticalSourceValue stage *
        toGaussian (ofNat common.denominator) := by
      rw [RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian_value]

private theorem criticalLowerError_ne_zero (stage : Nat) :
    criticalLowerError stage ≠ 0 := by
  unfold criticalLowerError
  apply RFAP.ConstructiveGaussian.Gaussian.neg_ne_zero_direct
  rw [← RFAP.ConstructiveGaussian.Gaussian.inv_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.inv_ne_zero_direct
  exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (criticalUpper_denominatorGaussian_ne_zero stage)
    (criticalGapVector_ne_zero (pellParameter_isFiniteCritical stage))

/-- The constructed source has the chosen lower division-free error. -/
theorem criticalSource_error_lower (stage : Nat) :
    error (criticalSource stage).value (criticalLowerPair stage) =
      criticalLowerError stage := by
  rw [criticalSource_value]
  unfold error criticalSourceValue
  calc
    ((toGaussian (criticalLowerPair stage).numerator +
          criticalLowerError stage) *
        RFAP.ConstructiveGaussian.Gaussian.inv
          (toGaussian (criticalLowerPair stage).denominator)) *
          toGaussian (criticalLowerPair stage).denominator -
        toGaussian (criticalLowerPair stage).numerator =
      (toGaussian (criticalLowerPair stage).numerator +
          criticalLowerError stage) *
        (RFAP.ConstructiveGaussian.Gaussian.inv
            (toGaussian (criticalLowerPair stage).denominator) *
          toGaussian (criticalLowerPair stage).denominator) -
        toGaussian (criticalLowerPair stage).numerator := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = (toGaussian (criticalLowerPair stage).numerator +
          criticalLowerError stage) * 1 -
        toGaussian (criticalLowerPair stage).numerator := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_mul _
        (criticalLower_denominatorGaussian_ne_zero stage)]
    _ = criticalLowerError stage := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1

private theorem criticalDesiredErrors_determinant (stage : Nat) :
    toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            criticalErrorRatio (pellParameter stage)) -
        toGaussian (criticalUpperPair stage).denominator *
          criticalLowerError stage = 1 := by
  have upperGapNonzero :
      toGaussian (criticalUpperPair stage).denominator *
          criticalGapVector (pellParameter stage) ≠ 0 :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (criticalUpper_denominatorGaussian_ne_zero stage)
      (criticalGapVector_ne_zero (pellParameter_isFiniteCritical stage))
  calc
    toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            criticalErrorRatio (pellParameter stage)) -
        toGaussian (criticalUpperPair stage).denominator *
          criticalLowerError stage =
      toGaussian (criticalUpperPair stage).denominator *
        (criticalDenominatorRatio (pellParameter stage) *
            criticalErrorRatio (pellParameter stage) - 1) *
          criticalLowerError stage := by
      rw [← criticalDenominatorRatio_mul_upper]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    _ =
      (toGaussian (criticalUpperPair stage).denominator *
          criticalGapVector (pellParameter stage)) *
        RFAP.ConstructiveGaussian.Gaussian.inv
          (toGaussian (criticalUpperPair stage).denominator *
            criticalGapVector (pellParameter stage)) := by
      unfold criticalLowerError criticalGapVector
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    _ = 1 :=
      RFAP.ConstructiveGaussian.Gaussian.mul_inv _ upperGapNonzero

/-- The upper division-free error has exactly the prescribed normalized
critical ratio. -/
theorem criticalSource_error_upper (stage : Nat) :
    error (criticalSource stage).value (criticalUpperPair stage) =
      criticalLowerError stage *
        criticalErrorRatio (pellParameter stage) := by
  have determinantIdentity :=
    toGaussian_coefficientDeterminant (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage)
  rw [criticalPair_determinant, toGaussian_one,
    criticalSource_error_lower] at determinantIdentity
  have desiredIdentity := criticalDesiredErrors_determinant stage
  have scaledEquality :
      toGaussian (criticalLowerPair stage).denominator *
          error (criticalSource stage).value (criticalUpperPair stage) =
        toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            criticalErrorRatio (pellParameter stage)) := by
    calc
      toGaussian (criticalLowerPair stage).denominator *
          error (criticalSource stage).value (criticalUpperPair stage) =
        (toGaussian (criticalLowerPair stage).denominator *
              error (criticalSource stage).value (criticalUpperPair stage) -
            toGaussian (criticalUpperPair stage).denominator *
              criticalLowerError stage) +
          toGaussian (criticalUpperPair stage).denominator *
            criticalLowerError stage := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = 1 + toGaussian (criticalUpperPair stage).denominator *
          criticalLowerError stage := by rw [← determinantIdentity]
      _ =
        (toGaussian (criticalLowerPair stage).denominator *
              (criticalLowerError stage *
                criticalErrorRatio (pellParameter stage)) -
            toGaussian (criticalUpperPair stage).denominator *
              criticalLowerError stage) +
          toGaussian (criticalUpperPair stage).denominator *
            criticalLowerError stage := by rw [desiredIdentity]
      _ = toGaussian (criticalLowerPair stage).denominator *
          (criticalLowerError stage *
            criticalErrorRatio (pellParameter stage)) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    (criticalLower_denominatorGaussian_ne_zero stage)
  calc
    error (criticalSource stage).value (criticalUpperPair stage) *
          toGaussian (criticalLowerPair stage).denominator =
        toGaussian (criticalLowerPair stage).denominator *
          error (criticalSource stage).value (criticalUpperPair stage) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]
    _ = toGaussian (criticalLowerPair stage).denominator *
        (criticalLowerError stage *
          criticalErrorRatio (pellParameter stage)) := scaledEquality
    _ = (criticalLowerError stage *
          criticalErrorRatio (pellParameter stage)) *
        toGaussian (criticalLowerPair stage).denominator := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]

private theorem criticalLower_normalized_boundary
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    (left right : GaussianInt) (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorBound :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) ≤ 1)
    (denominatorBound :
      normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) ≤ criticalCoordinateNorm value) :
    normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) = 1 ∧
      normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) = criticalCoordinateNorm value := by
  have coordinateLtOne := criticalCoordinateNorm_lt_one certificate
  have denominatorBoundOne :
      normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) ≤ 1 := denominatorBound.trans coordinateLtOne.le
  have small := coefficient_normNat_lt_four_of_critical_inside
    certificate left right errorBound denominatorBoundOne
  by_cases leftZero : left = 0
  · have rightNonzero : right ≠ 0 := by
      rcases coefficientNonzero with impossible | rightNonzero
      · exact (impossible leftZero).elim
      · exact rightNonzero
    have oneLeRight : 1 ≤ normNat right :=
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos rightNonzero
    have oneLeDenominator :
        (1 : Coordinate) ≤
          normSq (toGaussian left * criticalDenominatorRatio value +
            toGaussian right) := by
      rw [leftZero, toGaussian_zero,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add, normSq_toGaussian]
      exact RFAP.ConstructiveFraction.natCast_le_direct oneLeRight
    exact (not_lt_of_ge
      (oneLeDenominator.trans denominatorBound) coordinateLtOne).elim
  · by_cases rightZero : right = 0
    · have oneLeLeft : 1 ≤ normNat left :=
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos leftZero
      have castLeftLeOne : (normNat left : Coordinate) ≤ 1 := by
        simpa only [rightZero, toGaussian_zero,
          RFAP.ConstructiveGaussian.Gaussian.zero_mul,
          RFAP.ConstructiveGaussian.Gaussian.add_zero,
          normSq_toGaussian] using errorBound
      have leftLeOne : normNat left ≤ 1 :=
        (RFAP.ConstructiveFraction.natCast_le_iff_direct).1 castLeftLeOne
      have leftNorm : normNat left = 1 :=
        Nat.le_antisymm leftLeOne oneLeLeft
      constructor
      · rw [rightZero, toGaussian_zero,
          RFAP.ConstructiveGaussian.Gaussian.zero_mul,
          RFAP.ConstructiveGaussian.Gaussian.add_zero, normSq_toGaussian,
          leftNorm, Nat.cast_one]
      · rw [rightZero, toGaussian_zero,
          RFAP.ConstructiveGaussian.Gaussian.add_zero, normSq_mul,
          normSq_toGaussian, normSq_criticalDenominatorRatio, leftNorm]
        ring1
    · rcases small_nonzero_coefficients_strictly_exterior
          certificate left right leftZero rightZero small.1 small.2 with
        errorExterior | denominatorExterior
      · exact (not_lt_of_ge errorBound errorExterior).elim
      · exact (not_lt_of_ge
          (denominatorBound.trans coordinateLtOne.le)
          denominatorExterior).elim

private theorem criticalUpper_normalized_boundary
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value)
    (left right : GaussianInt) (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorBound :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) ≤
          criticalCoordinateNorm value)
    (denominatorBound :
      normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) ≤ 1) :
    normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) =
          criticalCoordinateNorm value ∧
      normSq (toGaussian left * criticalDenominatorRatio value +
        toGaussian right) = 1 := by
  have coordinateLtOne := criticalCoordinateNorm_lt_one certificate
  have errorBoundOne :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio value) ≤ 1 :=
    errorBound.trans coordinateLtOne.le
  have small := coefficient_normNat_lt_four_of_critical_inside
    certificate left right errorBoundOne denominatorBound
  by_cases rightZero : right = 0
  · have leftNonzero : left ≠ 0 := by
      rcases coefficientNonzero with leftNonzero | impossible
      · exact leftNonzero
      · exact (impossible rightZero).elim
    have oneLeLeft : 1 ≤ normNat left :=
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos leftNonzero
    have oneLeError :
        (1 : Coordinate) ≤
          normSq (toGaussian left +
            toGaussian right * criticalErrorRatio value) := by
      rw [rightZero, toGaussian_zero,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.add_zero, normSq_toGaussian]
      exact RFAP.ConstructiveFraction.natCast_le_direct oneLeLeft
    exact (not_lt_of_ge
      (oneLeError.trans errorBound) coordinateLtOne).elim
  · by_cases leftZero : left = 0
    · have oneLeRight : 1 ≤ normNat right :=
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos rightZero
      have castRightLeOne : (normNat right : Coordinate) ≤ 1 := by
        simpa only [leftZero, toGaussian_zero,
          RFAP.ConstructiveGaussian.Gaussian.zero_mul,
          RFAP.ConstructiveGaussian.Gaussian.zero_add,
          normSq_toGaussian] using denominatorBound
      have rightLeOne : normNat right ≤ 1 :=
        (RFAP.ConstructiveFraction.natCast_le_iff_direct).1 castRightLeOne
      have rightNorm : normNat right = 1 :=
        Nat.le_antisymm rightLeOne oneLeRight
      constructor
      · rw [leftZero, toGaussian_zero,
          RFAP.ConstructiveGaussian.Gaussian.zero_add, normSq_mul,
          normSq_toGaussian, normSq_criticalErrorRatio, rightNorm]
        ring1
      · rw [leftZero, toGaussian_zero,
          RFAP.ConstructiveGaussian.Gaussian.zero_mul,
          RFAP.ConstructiveGaussian.Gaussian.zero_add, normSq_toGaussian,
          rightNorm, Nat.cast_one]
    · rcases small_nonzero_coefficients_strictly_exterior
          certificate left right leftZero rightZero small.1 small.2 with
        errorExterior | denominatorExterior
      · exact (not_lt_of_ge
          (errorBound.trans coordinateLtOne.le) errorExterior).elim
      · exact (not_lt_of_ge denominatorBound denominatorExterior).elim

private theorem critical_error_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    error (criticalSource stage).value
        (linearCombination (criticalLowerPair stage)
          (criticalUpperPair stage) left right) =
      criticalLowerError stage *
        (toGaussian left + toGaussian right *
          criticalErrorRatio (pellParameter stage)) := by
  rw [error_linearCombination, criticalSource_error_lower,
    criticalSource_error_upper]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem critical_denominator_linearCombination
    (stage : Nat) (left right : GaussianInt) :
    toGaussian
        (linearCombination (criticalLowerPair stage)
          (criticalUpperPair stage) left right).denominator =
      toGaussian (criticalUpperPair stage).denominator *
        (toGaussian left * criticalDenominatorRatio (pellParameter stage) +
          toGaussian right) := by
  simp only [linearCombination, toGaussian_add, toGaussian_mul]
  rw [← criticalDenominatorRatio_mul_upper]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem coefficientNonzero_of_expansion
    (stage : Nat) (candidate : Pair) (candidateNonzero : PairNonzero candidate)
    (left right : GaussianInt)
    (expansion :
      linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right = candidate) :
    left ≠ 0 ∨ right ≠ 0 := by
  by_cases leftZero : left = 0
  · right
    intro rightZero
    have candidateZero : candidate = zeroPair := by
      calc
        candidate = linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right := expansion.symm
        _ = zeroPair := by
          rw [leftZero, rightZero]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
              simp only [linearCombination, zeroPair,
                RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im] <;>
              ring1
    rcases candidateNonzero with numeratorNonzero | denominatorNonzero
    · exact numeratorNonzero
        (congrArg (fun pair : Pair => pair.numerator) candidateZero)
    · exact denominatorNonzero
        (congrArg (fun pair : Pair => pair.denominator) candidateZero)
  · exact Or.inl leftZero

private theorem criticalLower_linearCombination_boundary
    (stage : Nat) (left right : GaussianInt)
    (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorInside :
      errorQuadrance (criticalSource stage).value
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        errorQuadrance (criticalSource stage).value
          (criticalLowerPair stage))
    (denominatorInside :
      denominatorQuadrance
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        denominatorQuadrance (criticalLowerPair stage)) :
    OnCylinderBoundary (criticalSource stage).value
      (criticalLowerPair stage)
      (linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right) := by
  have lowerErrorPositive : 0 < normSq (criticalLowerError stage) :=
    normSq_pos (criticalLowerError_ne_zero stage)
  have upperDenominatorPositive :
      0 < normSq (toGaussian (criticalUpperPair stage).denominator) :=
    normSq_pos (criticalUpper_denominatorGaussian_ne_zero stage)
  have normalizedErrorBound :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio (pellParameter stage)) ≤ 1 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := normSq (criticalLowerError stage))
    · calc
        normSq (toGaussian left +
              toGaussian right * criticalErrorRatio (pellParameter stage)) *
            normSq (criticalLowerError stage) =
          errorQuadrance (criticalSource stage).value
            (linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) := by
            unfold errorQuadrance
            rw [critical_error_linearCombination, normSq_mul]
            ring1
        _ ≤ errorQuadrance (criticalSource stage).value
            (criticalLowerPair stage) := errorInside
        _ = (1 : Coordinate) * normSq (criticalLowerError stage) := by
          unfold errorQuadrance
          rw [criticalSource_error_lower]
          ring1
    · exact lowerErrorPositive
  have normalizedDenominatorBound :
      normSq (toGaussian left *
          criticalDenominatorRatio (pellParameter stage) + toGaussian right) ≤
        criticalCoordinateNorm (pellParameter stage) := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := normSq (toGaussian (criticalUpperPair stage).denominator))
    · calc
        normSq (toGaussian left *
              criticalDenominatorRatio (pellParameter stage) +
            toGaussian right) *
            normSq (toGaussian (criticalUpperPair stage).denominator) =
          (denominatorQuadrance
            (linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) : Coordinate) := by
            unfold denominatorQuadrance
            rw [← normSq_toGaussian,
              critical_denominator_linearCombination, normSq_mul]
            ring1
        _ ≤ (denominatorQuadrance (criticalLowerPair stage) : Coordinate) :=
          RFAP.ConstructiveFraction.natCast_le_direct denominatorInside
        _ = criticalCoordinateNorm (pellParameter stage) *
            normSq (toGaussian (criticalUpperPair stage).denominator) := by
          unfold denominatorQuadrance
          rw [← normSq_toGaussian,
            ← criticalDenominatorRatio_mul_upper, normSq_mul,
            normSq_criticalDenominatorRatio]
    · exact upperDenominatorPositive
  have normalizedBoundary := criticalLower_normalized_boundary
    (pellParameter_isFiniteCritical stage) left right coefficientNonzero
      normalizedErrorBound normalizedDenominatorBound
  constructor
  · unfold errorQuadrance
    rw [critical_error_linearCombination, criticalSource_error_lower,
      normSq_mul, normalizedBoundary.1]
    ring1
  · apply RFAP.ConstructiveFraction.natCast_injective_direct
    unfold denominatorQuadrance
    rw [← normSq_toGaussian, ← normSq_toGaussian,
      critical_denominator_linearCombination,
      ← criticalDenominatorRatio_mul_upper,
      normSq_mul, normSq_mul, normSq_criticalDenominatorRatio,
      normalizedBoundary.2]
    ring1

private theorem criticalUpper_linearCombination_boundary
    (stage : Nat) (left right : GaussianInt)
    (coefficientNonzero : left ≠ 0 ∨ right ≠ 0)
    (errorInside :
      errorQuadrance (criticalSource stage).value
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        errorQuadrance (criticalSource stage).value
          (criticalUpperPair stage))
    (denominatorInside :
      denominatorQuadrance
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        denominatorQuadrance (criticalUpperPair stage)) :
    OnCylinderBoundary (criticalSource stage).value
      (criticalUpperPair stage)
      (linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right) := by
  have lowerErrorPositive : 0 < normSq (criticalLowerError stage) :=
    normSq_pos (criticalLowerError_ne_zero stage)
  have upperDenominatorPositive :
      0 < normSq (toGaussian (criticalUpperPair stage).denominator) :=
    normSq_pos (criticalUpper_denominatorGaussian_ne_zero stage)
  have normalizedErrorBound :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio (pellParameter stage)) ≤
          criticalCoordinateNorm (pellParameter stage) := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := normSq (criticalLowerError stage))
    · calc
        normSq (toGaussian left +
              toGaussian right * criticalErrorRatio (pellParameter stage)) *
            normSq (criticalLowerError stage) =
          errorQuadrance (criticalSource stage).value
            (linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) := by
            unfold errorQuadrance
            rw [critical_error_linearCombination, normSq_mul]
            ring1
        _ ≤ errorQuadrance (criticalSource stage).value
            (criticalUpperPair stage) := errorInside
        _ = criticalCoordinateNorm (pellParameter stage) *
            normSq (criticalLowerError stage) := by
          unfold errorQuadrance
          rw [criticalSource_error_upper, normSq_mul,
            normSq_criticalErrorRatio]
          ring1
    · exact lowerErrorPositive
  have normalizedDenominatorBound :
      normSq (toGaussian left *
          criticalDenominatorRatio (pellParameter stage) + toGaussian right) ≤
        1 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := normSq (toGaussian (criticalUpperPair stage).denominator))
    · calc
        normSq (toGaussian left *
              criticalDenominatorRatio (pellParameter stage) +
            toGaussian right) *
            normSq (toGaussian (criticalUpperPair stage).denominator) =
          (denominatorQuadrance
            (linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) : Coordinate) := by
            unfold denominatorQuadrance
            rw [← normSq_toGaussian,
              critical_denominator_linearCombination, normSq_mul]
            ring1
        _ ≤ (denominatorQuadrance (criticalUpperPair stage) : Coordinate) :=
          RFAP.ConstructiveFraction.natCast_le_direct denominatorInside
        _ = (1 : Coordinate) *
            normSq (toGaussian (criticalUpperPair stage).denominator) := by
          unfold denominatorQuadrance
          rw [← normSq_toGaussian]
          ring1
    · exact upperDenominatorPositive
  have normalizedBoundary := criticalUpper_normalized_boundary
    (pellParameter_isFiniteCritical stage) left right coefficientNonzero
      normalizedErrorBound normalizedDenominatorBound
  constructor
  · unfold errorQuadrance
    rw [critical_error_linearCombination, criticalSource_error_upper,
      normSq_mul, normSq_mul, normSq_criticalErrorRatio,
      normalizedBoundary.1]
  · apply RFAP.ConstructiveFraction.natCast_injective_direct
    unfold denominatorQuadrance
    rw [← normSq_toGaussian, ← normSq_toGaussian,
      critical_denominator_linearCombination, normSq_mul,
      normalizedBoundary.2]
    ring1

private theorem exists_critical_coefficients (stage : Nat) (candidate : Pair) :
    ∃ left right : GaussianInt,
      linearCombination (criticalLowerPair stage)
        (criticalUpperPair stage) left right = candidate := by
  let determinantValue := coefficientDeterminant
    (criticalLowerPair stage) (criticalUpperPair stage)
  refine ⟨conj determinantValue *
      coefficientDeterminant candidate (criticalUpperPair stage),
    conj determinantValue *
      coefficientDeterminant (criticalLowerPair stage) candidate, ?_⟩
  exact linearCombination_cramer_of_index_one
    (criticalLowerPair stage) (criticalUpperPair stage) candidate
      (criticalPair_indexOne stage)

/-- The lower endpoint of every finite critical window is a genuine best
approximation in the two-tier sense. -/
theorem criticalLower_isBest (stage : Nat) :
    IsBest (criticalSource stage).value (criticalLowerPair stage) := by
  apply (isBest_iff_isGaussLatticeMinimal
    (criticalSource stage).value (criticalLowerPair stage)).2
  refine ⟨criticalLower_denominator_ne_zero stage, ?_⟩
  intro candidate candidateNonzero inside
  rcases exists_critical_coefficients stage candidate with
    ⟨left, right, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion
    stage candidate candidateNonzero left right expansion
  have errorInside :
      errorQuadrance (criticalSource stage).value
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        errorQuadrance (criticalSource stage).value
          (criticalLowerPair stage) := by
    rw [expansion]
    exact inside.1
  have denominatorInside :
      denominatorQuadrance
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        denominatorQuadrance (criticalLowerPair stage) := by
    rw [expansion]
    exact inside.2
  have boundary := criticalLower_linearCombination_boundary stage left right
    coefficientNonzero errorInside denominatorInside
  rw [expansion] at boundary
  exact boundary

/-- The upper endpoint of every finite critical window is also best. -/
theorem criticalUpper_isBest (stage : Nat) :
    IsBest (criticalSource stage).value (criticalUpperPair stage) := by
  apply (isBest_iff_isGaussLatticeMinimal
    (criticalSource stage).value (criticalUpperPair stage)).2
  refine ⟨criticalUpper_denominator_ne_zero stage, ?_⟩
  intro candidate candidateNonzero inside
  rcases exists_critical_coefficients stage candidate with
    ⟨left, right, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion
    stage candidate candidateNonzero left right expansion
  have errorInside :
      errorQuadrance (criticalSource stage).value
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        errorQuadrance (criticalSource stage).value
          (criticalUpperPair stage) := by
    rw [expansion]
    exact inside.1
  have denominatorInside :
      denominatorQuadrance
          (linearCombination (criticalLowerPair stage)
            (criticalUpperPair stage) left right) ≤
        denominatorQuadrance (criticalUpperPair stage) := by
    rw [expansion]
    exact inside.2
  have boundary := criticalUpper_linearCombination_boundary stage left right
    coefficientNonzero errorInside denominatorInside
  rw [expansion] at boundary
  exact boundary

private theorem critical_mixedCylinderEmpty (stage : Nat) :
    MixedCylinderEmpty (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage) := by
  intro candidate candidateNonzero inside
  rcases exists_critical_coefficients stage candidate with
    ⟨left, right, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion
    stage candidate candidateNonzero left right expansion
  have lowerErrorPositive : 0 < normSq (criticalLowerError stage) :=
    normSq_pos (criticalLowerError_ne_zero stage)
  have upperDenominatorPositive :
      0 < normSq (toGaussian (criticalUpperPair stage).denominator) :=
    normSq_pos (criticalUpper_denominatorGaussian_ne_zero stage)
  have normalizedErrorInside :
      normSq (toGaussian left +
        toGaussian right * criticalErrorRatio (pellParameter stage)) < 1 := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := normSq (criticalLowerError stage))
    · calc
        normSq (toGaussian left +
              toGaussian right * criticalErrorRatio (pellParameter stage)) *
            normSq (criticalLowerError stage) =
          errorQuadrance (criticalSource stage).value
            (linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) := by
            unfold errorQuadrance
            rw [critical_error_linearCombination, normSq_mul]
            ring1
        _ = errorQuadrance (criticalSource stage).value candidate := by
          rw [expansion]
        _ < errorQuadrance (criticalSource stage).value
            (criticalLowerPair stage) := inside.1
        _ = (1 : Coordinate) * normSq (criticalLowerError stage) := by
          unfold errorQuadrance
          rw [criticalSource_error_lower]
          ring1
    · exact lowerErrorPositive
  have normalizedDenominatorInside :
      normSq (toGaussian left *
        criticalDenominatorRatio (pellParameter stage) + toGaussian right) <
          1 := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := normSq (toGaussian (criticalUpperPair stage).denominator))
    · calc
        normSq (toGaussian left *
              criticalDenominatorRatio (pellParameter stage) +
            toGaussian right) *
            normSq (toGaussian (criticalUpperPair stage).denominator) =
          (denominatorQuadrance
            (linearCombination (criticalLowerPair stage)
              (criticalUpperPair stage) left right) : Coordinate) := by
            unfold denominatorQuadrance
            rw [← normSq_toGaussian,
              critical_denominator_linearCombination, normSq_mul]
            ring1
        _ = (denominatorQuadrance candidate : Coordinate) := by rw [expansion]
        _ < (denominatorQuadrance (criticalUpperPair stage) : Coordinate) :=
          RFAP.ConstructiveFraction.natCast_lt_direct inside.2
        _ = (1 : Coordinate) *
            normSq (toGaussian (criticalUpperPair stage).denominator) := by
          unfold denominatorQuadrance
          rw [← normSq_toGaussian]
          ring1
    · exact upperDenominatorPositive
  rcases criticalCylinderExterior (pellParameter_isFiniteCritical stage)
      left right coefficientNonzero with errorExterior | denominatorExterior
  · exact (not_lt_of_ge errorExterior normalizedErrorInside)
  · exact (not_lt_of_ge denominatorExterior normalizedDenominatorInside)

/-- Each displayed Pell stage is an actual consecutive pair of best
approximations for its explicitly constructed rational source. -/
theorem criticalPairs_areConsecutiveBest (stage : Nat) :
    AreConsecutiveBest (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage) := by
  apply (areConsecutiveBest_iff_mixedCylinderEmpty
    (criticalSource stage) (criticalLowerPair stage)
      (criticalUpperPair stage)).2
  exact ⟨criticalLower_isBest stage, criticalUpper_isBest stage,
    critical_denominatorQuadrance_ordered stage,
    critical_mixedCylinderEmpty stage⟩

/-- The normalized gap and the actual squared Dirichlet window are exact
reciprocals. -/
theorem criticalGap_mul_dirichletWindow (stage : Nat) :
    criticalGap (pellParameter stage) *
      dirichletWindowQuadrance (criticalSource stage).value
        (criticalLowerPair stage) (criticalUpperPair stage) = 1 := by
  have productNonzero :
      toGaussian (criticalUpperPair stage).denominator *
          criticalGapVector (pellParameter stage) ≠ 0 :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (criticalUpper_denominatorGaussian_ne_zero stage)
      (criticalGapVector_ne_zero (pellParameter_isFiniteCritical stage))
  have productNormNonzero :
      normSq (toGaussian (criticalUpperPair stage).denominator *
        criticalGapVector (pellParameter stage)) ≠ 0 :=
    fun zero => productNonzero (normSq_eq_zero.mp zero)
  unfold dirichletWindowQuadrance denominatorQuadrance errorQuadrance
  rw [criticalSource_error_lower, ← normSq_toGaussian]
  unfold criticalLowerError criticalGap
  rw [normSq_neg,
    RFAP.ConstructiveGaussian.Gaussian.normSq_inv _ productNonzero,
    normSq_mul]
  change
    normSq (criticalGapVector (pellParameter stage)) *
        (normSq (toGaussian (criticalUpperPair stage).denominator) *
          (normSq (toGaussian (criticalUpperPair stage).denominator) *
            normSq (criticalGapVector (pellParameter stage)))⁻¹) = 1
  calc
    normSq (criticalGapVector (pellParameter stage)) *
          (normSq (toGaussian (criticalUpperPair stage).denominator) *
            (normSq (toGaussian (criticalUpperPair stage).denominator) *
              normSq (criticalGapVector (pellParameter stage)))⁻¹) =
        (normSq (criticalGapVector (pellParameter stage)) *
            normSq (toGaussian (criticalUpperPair stage).denominator)) *
          (normSq (toGaussian (criticalUpperPair stage).denominator) *
            normSq (criticalGapVector (pellParameter stage)))⁻¹ :=
      (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
    _ = (normSq (toGaussian (criticalUpperPair stage).denominator) *
            normSq (criticalGapVector (pellParameter stage))) *
          (normSq (toGaussian (criticalUpperPair stage).denominator) *
            normSq (criticalGapVector (pellParameter stage)))⁻¹ := by
      rw [RFAP.ConstructiveFraction.mul_comm
        (normSq (criticalGapVector (pellParameter stage)))]
    _ = normSq (toGaussian (criticalUpperPair stage).denominator *
            criticalGapVector (pellParameter stage)) *
          (normSq (toGaussian (criticalUpperPair stage).denominator *
            criticalGapVector (pellParameter stage)))⁻¹ := by
      rw [normSq_mul]
    _ = 1 := RFAP.ConstructiveFraction.mul_inv_cancel _ productNormNonzero

/-- Exact rational factorization of the critical gap.  Clearing the fixed
denominator `16` avoids introducing the omitted quadratic endpoint. -/
theorem criticalGap_scaled_factorization (value : Coordinate) :
    criticalGap value * 16 =
      48 * value +
        parameterPolynomial value * (value ^ 2 + 4 * value + 17) := by
  calc
    criticalGap value * 16 =
        48 * value +
          parameterPolynomial value * (value ^ 2 + 4 * value + 17) +
          (4 * half ^ 2 - 1) *
            ((4 * half ^ 2 + 1) * (1 + value ^ 2) ^ 2 -
              16 * value) := by
      rw [criticalGap_eq]
      unfold parameterPolynomial
      ring1
    _ = 48 * value +
        parameterPolynomial value * (value ^ 2 + 4 * value + 17) := by
      rw [four_mul_half_sq]
      ring1

/-- A coarse but convenient strict defect estimate.  Its slack is ample on
`1/4 ≤ s < 1/3`, and its denominator-free form composes cleanly with the
Pell identity. -/
theorem criticalGap_lt_three_parameter_add_two_defects
    {value : Coordinate} (certificate : IsFiniteCriticalParameter value) :
    criticalGap value <
      3 * value + 2 * parameterPolynomial value := by
  have valueNonnegative := criticalParameter_nonnegative certificate
  have valueLtOne : value < (1 : Coordinate) :=
    certificate.2.1.trans (by decide)
  have squareLeOne : value ^ 2 ≤ (1 : Coordinate) := by
    have valueLeOne := valueLtOne.le
    simpa only [one_pow] using
      RFAP.ConstructiveFraction.pow_le_pow_direct valueNonnegative valueLeOne 2
  have fourValueLtTwo : 4 * value < (2 : Coordinate) := by
    calc
      4 * value < 4 * (1 / 3 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) certificate.2.1
      _ < 2 := by decide
  have factorLtThirtyTwo :
      value ^ 2 + 4 * value + 17 < (32 : Coordinate) := by
    calc
      value ^ 2 + 4 * value + 17 ≤ 1 + 4 * value + 17 :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          (RFAP.ConstructiveFraction.add_le_add_right_direct
            squareLeOne (4 * value)) 17
      _ < 1 + 2 + 17 :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (RFAP.ConstructiveFraction.add_lt_add_left_direct
            fourValueLtTwo 1) 17
      _ = 20 := by ring1
      _ < 32 := by
        simpa only [Nat.cast_ofNat] using
          RFAP.ConstructiveFraction.natCast_lt_direct
            (show 20 < 32 by decide)
  have defectScaledStrict :
      parameterPolynomial value * (value ^ 2 + 4 * value + 17) <
        parameterPolynomial value * 32 :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      certificate.2.2 factorLtThirtyTwo
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 16)
  · calc
      criticalGap value * 16 =
          48 * value + parameterPolynomial value *
            (value ^ 2 + 4 * value + 17) :=
        criticalGap_scaled_factorization value
      _ < 48 * value + parameterPolynomial value * 32 :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          defectScaledStrict (48 * value)
      _ = (3 * value + 2 * parameterPolynomial value) * 16 := by
        ring1
  · simpa only [Nat.cast_ofNat] using
      RFAP.ConstructiveFraction.natCast_pos_direct
        (show 0 < 16 by decide)

/-- Polynomial whose smaller omitted zero is the optimal rational-window
threshold. -/
def windowBoundaryPolynomial (threshold : Coordinate) : Coordinate :=
  threshold ^ 2 - 12 * threshold + 9

/-- A displayed threshold on the sharper side of the optimal boundary. -/
def IsSharperWindowThreshold (threshold : Coordinate) : Prop :=
  (3 / 4 : Coordinate) ≤ threshold ∧ threshold < 1 ∧
    windowBoundaryPolynomial threshold < 0

private theorem thresholdParameter_mul_three (threshold : Coordinate) :
    (threshold / 3) * 3 = threshold :=
  RFAP.ConstructiveFraction.div_mul_cancel_of_ne threshold 3 (by decide)

theorem parameterPolynomial_thresholdParameter_scaled
    (threshold : Coordinate) :
    parameterPolynomial (threshold / 3) * 9 =
      windowBoundaryPolynomial threshold := by
  calc
    parameterPolynomial (threshold / 3) * 9 =
        ((threshold / 3) * 3) ^ 2 -
          4 * ((threshold / 3) * 3) * 3 + 9 := by
      unfold parameterPolynomial
      ring1
    _ = windowBoundaryPolynomial threshold := by
      rw [thresholdParameter_mul_three]
      unfold windowBoundaryPolynomial
      ring1

private theorem sharperThreshold_parameter_nonnegative
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold) :
    0 ≤ threshold / 3 := by
  have thresholdNonnegative : (0 : Coordinate) ≤ threshold :=
    (show (0 : Coordinate) ≤ 3 / 4 by decide).trans certificate.1
  exact RFAP.ConstructiveFraction.div_nonneg_direct thresholdNonnegative
    (by decide)

private theorem sharperThreshold_parameter_lt_oneThird
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold) :
    threshold / 3 < (1 / 3 : Coordinate) := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos (by decide)).2
  calc
    threshold < 1 := certificate.2.1
    _ = (1 / 3 : Coordinate) * 3 := by decide

private theorem sharperThreshold_parameterPolynomial_neg
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold) :
    parameterPolynomial (threshold / 3) < 0 := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 9)
  · calc
      parameterPolynomial (threshold / 3) * 9 =
          windowBoundaryPolynomial threshold :=
        parameterPolynomial_thresholdParameter_scaled threshold
      _ < 0 := certificate.2.2
      _ = (0 : Coordinate) * 9 := by ring1
  · decide

private theorem parameterPolynomial_difference
    (left right : Coordinate) :
    parameterPolynomial left - parameterPolynomial right =
      (right - left) * (4 - right - left) := by
  unfold parameterPolynomial
  ring1

private theorem pellParameter_lt_thresholdParameter
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (stage : Nat) :
    pellParameter stage < threshold / 3 := by
  have leftPositive := parameterPolynomial_pellParameter_pos stage
  have rightNegative := sharperThreshold_parameterPolynomial_neg certificate
  have polynomialDifferencePositive :
      0 < parameterPolynomial (pellParameter stage) -
        parameterPolynomial (threshold / 3) :=
    RFAP.ConstructiveFraction.sub_pos_direct
      (rightNegative.trans leftPositive)
  have parameterSumLtFour :
      threshold / 3 + pellParameter stage < (4 : Coordinate) := by
    calc
      threshold / 3 + pellParameter stage <
          (1 / 3 : Coordinate) + 1 / 3 :=
        RFAP.ConstructiveFraction.add_lt_add_direct
          (sharperThreshold_parameter_lt_oneThird certificate)
          (pellParameter_isFiniteCritical stage).2.1
      _ < 4 := by decide
  have factorPositive :
      0 < 4 - threshold / 3 - pellParameter stage := by
    have differencePositive :=
      RFAP.ConstructiveFraction.sub_pos_direct parameterSumLtFour
    calc
      (0 : Coordinate) < 4 - (threshold / 3 + pellParameter stage) :=
        differencePositive
      _ = 4 - threshold / 3 - pellParameter stage := by ring1
  have productPositive :
      0 < (4 - threshold / 3 - pellParameter stage) *
        (threshold / 3 - pellParameter stage) := by
    calc
      (0 : Coordinate) <
          parameterPolynomial (pellParameter stage) -
            parameterPolynomial (threshold / 3) :=
        polynomialDifferencePositive
      _ = (4 - threshold / 3 - pellParameter stage) *
          (threshold / 3 - pellParameter stage) := by
        rw [parameterPolynomial_difference]
        ring1
  exact RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    (RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      productPositive factorPositive.le)

private theorem boundaryClearance_lt_twelve_parameterMargin
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (stage : Nat) :
    -windowBoundaryPolynomial threshold <
      12 * (threshold - 3 * pellParameter stage) := by
  let sourceParameter := pellParameter stage
  let thresholdParameter := threshold / 3
  have sourcePositive := parameterPolynomial_pellParameter_pos stage
  have parameterOrder : sourceParameter < thresholdParameter :=
    pellParameter_lt_thresholdParameter certificate stage
  have differencePositive : 0 < thresholdParameter - sourceParameter :=
    RFAP.ConstructiveFraction.sub_pos_direct parameterOrder
  have thresholdNonnegative :=
    sharperThreshold_parameter_nonnegative certificate
  have sourceNonnegative :=
    criticalParameter_nonnegative (pellParameter_isFiniteCritical stage)
  have sumNonnegative : 0 ≤ thresholdParameter + sourceParameter :=
    add_nonneg thresholdNonnegative sourceNonnegative
  have factorLeFour :
      4 - thresholdParameter - sourceParameter ≤ (4 : Coordinate) := by
    calc
      4 - thresholdParameter - sourceParameter =
          4 - (thresholdParameter + sourceParameter) := by ring1
      _ ≤ 4 := sub_le_self 4 sumNonnegative
  have firstStrict :
      -windowBoundaryPolynomial threshold <
        9 * (parameterPolynomial sourceParameter -
          parameterPolynomial thresholdParameter) := by
    have scaledSourcePositive :
        0 < 9 * parameterPolynomial sourceParameter :=
      RFAP.ConstructiveFraction.mul_pos_direct (by decide) sourcePositive
    calc
      -windowBoundaryPolynomial threshold =
          -(parameterPolynomial thresholdParameter * 9) := by
        rw [parameterPolynomial_thresholdParameter_scaled]
      _ < 9 * parameterPolynomial sourceParameter -
          9 * parameterPolynomial thresholdParameter := by
        apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
        calc
          (0 : Coordinate) < 9 * parameterPolynomial sourceParameter :=
            scaledSourcePositive
          _ =
              (9 * parameterPolynomial sourceParameter -
                  9 * parameterPolynomial thresholdParameter) -
                -(parameterPolynomial thresholdParameter * 9) := by ring1
      _ = 9 * (parameterPolynomial sourceParameter -
          parameterPolynomial thresholdParameter) := by ring1
  calc
    -windowBoundaryPolynomial threshold <
        9 * (parameterPolynomial sourceParameter -
          parameterPolynomial thresholdParameter) := firstStrict
    _ = 9 * (thresholdParameter - sourceParameter) *
        (4 - thresholdParameter - sourceParameter) := by
      rw [parameterPolynomial_difference]
      ring1
    _ ≤ 9 * (thresholdParameter - sourceParameter) * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct factorLeFour
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          differencePositive.le)
    _ = 12 * ((threshold / 3) * 3 -
        3 * pellParameter stage) := by
      dsimp only [thresholdParameter, sourceParameter]
      ring1
    _ = 12 * (threshold - 3 * pellParameter stage) := by
      rw [thresholdParameter_mul_three]

private theorem boundaryNegation_pos
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold) :
    0 < -windowBoundaryPolynomial threshold := by
  calc
    (0 : Coordinate) < 0 - windowBoundaryPolynomial threshold :=
      RFAP.ConstructiveFraction.sub_pos_direct certificate.2.2
    _ = -windowBoundaryPolynomial threshold := by ring1

/-- A wholly explicit stage index.  The first summand makes the Pell defect
small enough; `requestedScale` then moves the witness beyond any supplied
finite scale. -/
def sharpnessStage (threshold : Coordinate) (requestedScale : Nat) : Nat :=
  RFAP.ConstructiveFraction.ceilNat
      (24 / -windowBoundaryPolynomial threshold) +
    requestedScale + 1

theorem requestedScale_lt_sharpnessStage
    (threshold : Coordinate) (requestedScale : Nat) :
    requestedScale < sharpnessStage threshold requestedScale := by
  unfold sharpnessStage
  exact Nat.lt_succ_of_le
    (Nat.le_add_left requestedScale
      (RFAP.ConstructiveFraction.ceilNat
        (24 / -windowBoundaryPolynomial threshold)))

private theorem sharpnessStage_clearance
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    (24 : Coordinate) <
      -windowBoundaryPolynomial threshold *
        (pellDenominator (sharpnessStage threshold requestedScale) :
          Coordinate) ^ 2 := by
  let delta := -windowBoundaryPolynomial threshold
  let ceiling := RFAP.ConstructiveFraction.ceilNat (24 / delta)
  let stage := sharpnessStage threshold requestedScale
  have deltaPositive : 0 < delta := boundaryNegation_pos certificate
  have ratioNonnegative : (0 : Coordinate) ≤ 24 / delta :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) deltaPositive).le
  have ratioLeCeiling :
      24 / delta ≤ (ceiling : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtStageNat : ceiling < stage := by
    dsimp only [ceiling, stage, delta, sharpnessStage]
    exact Nat.lt_succ_of_le
      (Nat.le_add_right
        (RFAP.ConstructiveFraction.ceilNat
          (24 / -windowBoundaryPolynomial threshold)) requestedScale)
  have ceilingLtStage :
      (ceiling : Coordinate) < (stage : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct ceilingLtStageNat
  have ratioLtStage : 24 / delta < (stage : Coordinate) :=
    ratioLeCeiling.trans_lt ceilingLtStage
  have twentyFourLtStageDelta :
      (24 : Coordinate) < (stage : Coordinate) * delta :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos deltaPositive).1 ratioLtStage
  have stageLtDenominatorNat :
      stage < pellDenominator stage := stage_lt_pellDenominator stage
  have stageLtDenominator :
      (stage : Coordinate) < (pellDenominator stage : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct stageLtDenominatorNat
  have stageDeltaLtDenominatorDelta :
      (stage : Coordinate) * delta <
        (pellDenominator stage : Coordinate) * delta :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      stageLtDenominator deltaPositive
  have denominatorLeSquareNat :
      pellDenominator stage ≤ pellDenominator stage ^ 2 := by
    have positive := pellDenominator_pos stage
    simpa only [pow_two] using
      Nat.le_mul_of_pos_right (pellDenominator stage) positive
  have denominatorLeSquare :
      (pellDenominator stage : Coordinate) ≤
        (pellDenominator stage ^ 2 : Nat) :=
    RFAP.ConstructiveFraction.natCast_le_direct denominatorLeSquareNat
  have denominatorDeltaLeSquareDelta :
      (pellDenominator stage : Coordinate) * delta ≤
        (pellDenominator stage : Coordinate) ^ 2 * delta := by
    have castPower :
        (pellDenominator stage ^ 2 : Nat) =
          (pellDenominator stage : Coordinate) ^ 2 := by
      rw [Nat.cast_pow]
    rw [← castPower]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      denominatorLeSquare deltaPositive.le
  calc
    (24 : Coordinate) <
        (sharpnessStage threshold requestedScale : Coordinate) *
          -windowBoundaryPolynomial threshold := by
      simpa only [stage, delta] using twentyFourLtStageDelta
    _ < (pellDenominator (sharpnessStage threshold requestedScale) :
          Coordinate) * -windowBoundaryPolynomial threshold :=
      by simpa only [stage, delta] using stageDeltaLtDenominatorDelta
    _ ≤ (pellDenominator (sharpnessStage threshold requestedScale) :
          Coordinate) ^ 2 * -windowBoundaryPolynomial threshold :=
      by simpa only [stage, delta] using denominatorDeltaLeSquareDelta
    _ = -windowBoundaryPolynomial threshold *
        (pellDenominator (sharpnessStage threshold requestedScale) :
          Coordinate) ^ 2 := by ring1

private theorem scaledPellDefect_lt_boundaryNegation
    {threshold : Coordinate} (stage : Nat)
    (clearance :
      (24 : Coordinate) < -windowBoundaryPolynomial threshold *
        (pellDenominator stage : Coordinate) ^ 2) :
    24 * parameterPolynomial (pellParameter stage) <
      -windowBoundaryPolynomial threshold := by
  have denominatorSquarePositive :
      0 < (pellDenominator stage : Coordinate) ^ 2 := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.mul_pos_direct
        (pellDenominator_cast_pos stage) (pellDenominator_cast_pos stage)
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (pellDenominator stage : Coordinate) ^ 2)
  · calc
      (24 * parameterPolynomial (pellParameter stage)) *
            (pellDenominator stage : Coordinate) ^ 2 =
          24 * (parameterPolynomial (pellParameter stage) *
            (pellDenominator stage : Coordinate) ^ 2) := by ring1
      _ = 24 := by rw [parameterPolynomial_pellParameter_scaled]; ring1
      _ < -windowBoundaryPolynomial threshold *
          (pellDenominator stage : Coordinate) ^ 2 := clearance
  · exact denominatorSquarePositive

private theorem criticalGap_lt_sharperThreshold_of_clearance
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (stage : Nat)
    (clearance :
      (24 : Coordinate) < -windowBoundaryPolynomial threshold *
        (pellDenominator stage : Coordinate) ^ 2) :
    criticalGap (pellParameter stage) < threshold := by
  have scaledDefect := scaledPellDefect_lt_boundaryNegation stage clearance
  have boundaryMargin := boundaryClearance_lt_twelve_parameterMargin
    certificate stage
  have twiceDefectLtMargin :
      2 * parameterPolynomial (pellParameter stage) <
        threshold - 3 * pellParameter stage := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 12)
    · calc
        (2 * parameterPolynomial (pellParameter stage)) * 12 =
            24 * parameterPolynomial (pellParameter stage) := by ring1
        _ < -windowBoundaryPolynomial threshold := scaledDefect
        _ < 12 * (threshold - 3 * pellParameter stage) := boundaryMargin
        _ = (threshold - 3 * pellParameter stage) * 12 := by ring1
    · decide
  calc
    criticalGap (pellParameter stage) <
        3 * pellParameter stage +
          2 * parameterPolynomial (pellParameter stage) :=
      criticalGap_lt_three_parameter_add_two_defects
        (pellParameter_isFiniteCritical stage)
    _ < 3 * pellParameter stage +
        (threshold - 3 * pellParameter stage) :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct
        twiceDefectLtMargin (3 * pellParameter stage)
    _ = threshold := by ring1

/-- At the explicit stage selected from a sharper rational threshold, the
normalized critical gap is already strictly below that threshold. -/
theorem criticalGap_lt_sharperThreshold
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    criticalGap
        (pellParameter (sharpnessStage threshold requestedScale)) < threshold :=
  criticalGap_lt_sharperThreshold_of_clearance certificate
    (sharpnessStage threshold requestedScale)
    (sharpnessStage_clearance certificate requestedScale)

/-- The explicitly selected Pell denominator lies beyond the requested
finite scale. -/
theorem requestedScale_lt_criticalDenominator
    (threshold : Coordinate) (requestedScale : Nat) :
    requestedScale <
      pellDenominator (sharpnessStage threshold requestedScale) :=
  (requestedScale_lt_sharpnessStage threshold requestedScale).trans
    (stage_lt_pellDenominator (sharpnessStage threshold requestedScale))

/-- The actual upper-pair denominator quadrance also lies beyond the supplied
natural scale. -/
theorem requestedScale_lt_criticalUpperDenominatorQuadrance
    (threshold : Coordinate) (requestedScale : Nat) :
    requestedScale < denominatorQuadrance
      (criticalUpperPair (sharpnessStage threshold requestedScale)) := by
  let stage := sharpnessStage threshold requestedScale
  have requestedLtDenominator : requestedScale < pellDenominator stage := by
    simpa only [stage] using
      requestedScale_lt_criticalDenominator threshold requestedScale
  have denominatorPositive := pellDenominator_pos stage
  have denominatorLeSquare :
      pellDenominator stage ≤ pellDenominator stage ^ 2 := by
    simpa only [pow_two] using
      Nat.le_mul_of_pos_right (pellDenominator stage) denominatorPositive
  have squarePositive : 0 < pellDenominator stage ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_pos denominatorPositive denominatorPositive
  rw [show criticalUpperPair (sharpnessStage threshold requestedScale) =
      criticalUpperPair stage by rfl,
    criticalUpper_denominatorQuadrance]
  exact requestedLtDenominator.trans_le denominatorLeSquare |>.trans (by
    simpa only [Nat.one_mul] using
      Nat.mul_lt_mul_of_pos_right (show 1 < 4 by decide) squarePositive)

private theorem criticalDirichletWindow_pos (stage : Nat) :
    0 < dirichletWindowQuadrance (criticalSource stage).value
      (criticalLowerPair stage) (criticalUpperPair stage) := by
  apply RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
  · calc
      (0 : Coordinate) < 1 := by decide
      _ = criticalGap (pellParameter stage) *
          dirichletWindowQuadrance (criticalSource stage).value
            (criticalLowerPair stage) (criticalUpperPair stage) :=
        (criticalGap_mul_dirichletWindow stage).symm
  · unfold criticalGap
    exact normSq_nonneg _

/-- Every sharper displayed rational threshold fails on an explicitly
constructed consecutive-best window beyond every supplied finite scale. -/
theorem one_lt_sharperThreshold_mul_criticalWindow
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    1 < threshold *
      dirichletWindowQuadrance
        (criticalSource (sharpnessStage threshold requestedScale)).value
        (criticalLowerPair (sharpnessStage threshold requestedScale))
        (criticalUpperPair (sharpnessStage threshold requestedScale)) := by
  let stage := sharpnessStage threshold requestedScale
  have gapStrict : criticalGap (pellParameter stage) < threshold := by
    simpa only [stage] using
      criticalGap_lt_sharperThreshold certificate requestedScale
  have windowPositive := criticalDirichletWindow_pos stage
  calc
    (1 : Coordinate) = criticalGap (pellParameter stage) *
        dirichletWindowQuadrance (criticalSource stage).value
          (criticalLowerPair stage) (criticalUpperPair stage) :=
      (criticalGap_mul_dirichletWindow stage).symm
    _ < threshold *
        dirichletWindowQuadrance (criticalSource stage).value
          (criticalLowerPair stage) (criticalUpperPair stage) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        gapStrict windowPositive

/-- Bundled paper-facing conclusion: the explicit denominator exceeds the
request, its endpoints are consecutive best approximations, and the proposed
sharper window inequality fails. -/
theorem finiteCriticalWindowSharpness
    {threshold : Coordinate} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    requestedScale < denominatorQuadrance
        (criticalUpperPair (sharpnessStage threshold requestedScale)) ∧
      AreConsecutiveBest
        (criticalSource (sharpnessStage threshold requestedScale)).value
        (criticalLowerPair (sharpnessStage threshold requestedScale))
        (criticalUpperPair (sharpnessStage threshold requestedScale)) ∧
      1 < threshold *
        dirichletWindowQuadrance
          (criticalSource (sharpnessStage threshold requestedScale)).value
          (criticalLowerPair (sharpnessStage threshold requestedScale))
          (criticalUpperPair (sharpnessStage threshold requestedScale)) := by
  exact ⟨requestedScale_lt_criticalUpperDenominatorQuadrance
      threshold requestedScale,
    criticalPairs_areConsecutiveBest _,
    one_lt_sharperThreshold_mul_criticalWindow certificate requestedScale⟩

end RFAP.FiniteWindowSharpness
