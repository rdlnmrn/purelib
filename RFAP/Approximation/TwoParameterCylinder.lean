import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.FiniteWindowSharpness

/-!
# Two-parameter finite critical cylinders

After one critical Pell basis transition, the normalized error coordinate
and normalized denominator coordinate generally carry different rational
parameters.  This module proves the cylinder exterior estimate uniformly
when both supplied parameters lie in the finite critical chamber.  The proof
uses a uniform rational coefficient bound followed by the same finite
unit/diagonal case split as the one-parameter critical cylinder.
-/

namespace RFAP.TwoParameterCylinder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

open RFAP.ConstructiveGaussianHeight.GaussianInt

private def half : Coordinate := 1 / 2

private theorem half_sq : half ^ 2 = (1 / 4 : Coordinate) := by
  unfold half
  decide

/-- Normalized upper error with its independently supplied parameter. -/
def errorRatio (value : Coordinate) : Gaussian :=
  ⟨half, half * value⟩

/-- Normalized lower denominator with its independently supplied parameter. -/
def denominatorRatio (value : Coordinate) : Gaussian :=
  ⟨half * value, -half⟩

@[simp] theorem errorRatio_re (value : Coordinate) :
    (errorRatio value).re = (1 / 2 : Coordinate) := by
  rfl

@[simp] theorem errorRatio_im (value : Coordinate) :
    (errorRatio value).im = (1 / 2 : Coordinate) * value := by
  rfl

@[simp] theorem denominatorRatio_re (value : Coordinate) :
    (denominatorRatio value).re = (1 / 2 : Coordinate) * value := by
  rfl

@[simp] theorem denominatorRatio_im (value : Coordinate) :
    (denominatorRatio value).im = -(1 / 2 : Coordinate) := by
  rfl

def normalizedError
    (errorParameter : Coordinate) (left right : GaussianInt) : Gaussian :=
  toGaussian left + toGaussian right * errorRatio errorParameter

def normalizedDenominator
    (denominatorParameter : Coordinate)
    (left right : GaussianInt) : Gaussian :=
  toGaussian left * denominatorRatio denominatorParameter + toGaussian right

def gapVector
    (errorParameter denominatorParameter : Coordinate) : Gaussian :=
  1 - denominatorRatio denominatorParameter * errorRatio errorParameter

def gap (errorParameter denominatorParameter : Coordinate) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
    (gapVector errorParameter denominatorParameter)

/-- On the diagonal, the two-parameter gap is the original critical gap. -/
theorem diagonalGap_eq_criticalGap (value : Coordinate) :
    gap value value = RFAP.FiniteWindowSharpness.criticalGap value := by
  rfl

theorem normSq_errorRatio (value : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (errorRatio value) =
      half ^ 2 + (half * value) ^ 2 := by
  rfl

theorem normSq_denominatorRatio (value : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (denominatorRatio value) =
      half ^ 2 + (half * value) ^ 2 := by
  unfold denominatorRatio RFAP.ConstructiveGaussian.Gaussian.normSq
  ring1

private theorem parameter_nonnegative
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 ≤ value :=
  (show (0 : Coordinate) ≤ 1 / 4 by decide).trans certificate.1

private theorem parameter_le_oneThird
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    value ≤ 1 / 3 := certificate.2.1.le

private theorem coordinateNorm_le_twentyThreeEighteenths
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    2 * (1 + RFAP.ConstructiveGaussian.Gaussian.normSq
      (errorRatio value)) ≤ 23 / 9 := by
  have scaledSquare : (half * value) ^ 2 ≤
      (half * (1 / 3 : Coordinate)) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (show (0 : Coordinate) ≤ half by unfold half; decide)
        (parameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (parameter_le_oneThird certificate)
        (show (0 : Coordinate) ≤ half by unfold half; decide)) 2
  rw [normSq_errorRatio]
  calc
    2 * (1 + (half ^ 2 + (half * value) ^ 2)) ≤
        2 * (1 + (half ^ 2 + (half * (1 / 3 : Coordinate)) ^ 2)) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · exact RFAP.ConstructiveFraction.add_le_add_direct (le_refl 1)
          (RFAP.ConstructiveFraction.add_le_add_direct (le_refl (half ^ 2))
            scaledSquare)
      · decide
    _ = 23 / 9 := by
      unfold half
      decide

private theorem coordinateNorm_denominator_le_twentyThreeEighteenths
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    2 * (1 + RFAP.ConstructiveGaussian.Gaussian.normSq
      (denominatorRatio value)) ≤ 23 / 9 := by
  rw [normSq_denominatorRatio]
  simpa only [normSq_errorRatio] using
    coordinateNorm_le_twentyThreeEighteenths certificate

/-- Every normalized error coordinate in the finite critical chamber lies
strictly inside the unit quadrance wall. -/
theorem normSq_errorRatio_lt_one
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (errorRatio value) < 1 := by
  have scaledSquare : (half * value) ^ 2 ≤
      (half * (1 / 3 : Coordinate)) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (show (0 : Coordinate) ≤ half by unfold half; decide)
        (parameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (parameter_le_oneThird certificate)
        (show (0 : Coordinate) ≤ half by unfold half; decide)) 2
  rw [normSq_errorRatio]
  calc
    half ^ 2 + (half * value) ^ 2 ≤
        half ^ 2 + (half * (1 / 3 : Coordinate)) ^ 2 :=
      RFAP.ConstructiveFraction.add_le_add_direct (le_refl (half ^ 2))
        scaledSquare
    _ < 1 := by
      unfold half
      decide

theorem gap_eq
    (errorParameter denominatorParameter : Coordinate) :
    gap errorParameter denominatorParameter =
      (1 - half ^ 2 * (errorParameter + denominatorParameter)) ^ 2 +
        (half ^ 2 * (1 - errorParameter * denominatorParameter)) ^ 2 := by
  unfold gap gapVector errorRatio denominatorRatio
  simp only [RFAP.ConstructiveGaussian.Gaussian.normSq,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.one_re,
    RFAP.ConstructiveGaussian.Gaussian.one_im]
  ring1

/-- Increasing either rational parameter within the finite critical chamber
can only decrease the exact two-parameter determinant gap. -/
theorem gap_antitone
    {errorLower errorUpper denominatorLower denominatorUpper : Coordinate}
    (errorUpperCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorUpper)
    (denominatorLowerCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter denominatorLower)
    (denominatorUpperCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter denominatorUpper)
    (errorOrder : errorLower ≤ errorUpper)
    (denominatorOrder : denominatorLower ≤ denominatorUpper) :
    gap errorUpper denominatorUpper ≤ gap errorLower denominatorLower := by
  have halfSquareNonnegative : (0 : Coordinate) ≤ half ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct half
  have upperSumBound :
      errorUpper + denominatorUpper ≤ (2 / 3 : Coordinate) := by
    calc
      errorUpper + denominatorUpper ≤ 1 / 3 + 1 / 3 :=
        RFAP.ConstructiveFraction.add_le_add_direct
          (parameter_le_oneThird errorUpperCertificate)
          (parameter_le_oneThird denominatorUpperCertificate)
      _ = 2 / 3 := by decide
  have sumOrder :
      errorLower + denominatorLower ≤
        errorUpper + denominatorUpper :=
    RFAP.ConstructiveFraction.add_le_add_direct errorOrder denominatorOrder
  have scaledSumOrder :
      half ^ 2 * (errorLower + denominatorLower) ≤
        half ^ 2 * (errorUpper + denominatorUpper) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sumOrder
      halfSquareNonnegative
  have upperScaledSumLeOne :
      half ^ 2 * (errorUpper + denominatorUpper) ≤ 1 := by
    calc
      half ^ 2 * (errorUpper + denominatorUpper) ≤
          half ^ 2 * (2 / 3 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          upperSumBound halfSquareNonnegative
      _ ≤ 1 := by
        rw [half_sq]
        decide
  have firstCoordinateNonnegative :
      (0 : Coordinate) ≤
        1 - half ^ 2 * (errorUpper + denominatorUpper) :=
    RFAP.ConstructiveFraction.sub_nonneg_direct upperScaledSumLeOne
  have firstCoordinateOrder :
      1 - half ^ 2 * (errorUpper + denominatorUpper) ≤
        1 - half ^ 2 * (errorLower + denominatorLower) :=
    RFAP.ConstructiveFraction.sub_le_sub_left_direct scaledSumOrder 1
  have firstSquareOrder :
      (1 - half ^ 2 * (errorUpper + denominatorUpper)) ^ 2 ≤
        (1 - half ^ 2 * (errorLower + denominatorLower)) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct firstCoordinateNonnegative
      firstCoordinateOrder 2
  have errorUpperNonnegative :=
    parameter_nonnegative errorUpperCertificate
  have denominatorLowerNonnegative :=
    parameter_nonnegative denominatorLowerCertificate
  have productOrder :
      errorLower * denominatorLower ≤
        errorUpper * denominatorUpper := by
    calc
      errorLower * denominatorLower ≤
          errorUpper * denominatorLower :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          errorOrder denominatorLowerNonnegative
      _ ≤ errorUpper * denominatorUpper :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorOrder errorUpperNonnegative
  have upperProductLeOne : errorUpper * denominatorUpper ≤ 1 := by
    calc
      errorUpper * denominatorUpper ≤
          (1 / 3 : Coordinate) * denominatorUpper :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (parameter_le_oneThird errorUpperCertificate)
          (parameter_nonnegative denominatorUpperCertificate)
      _ ≤ (1 / 3 : Coordinate) * (1 / 3 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (parameter_le_oneThird denominatorUpperCertificate) (by decide)
      _ ≤ 1 := by decide
  have upperComplementNonnegative :
      (0 : Coordinate) ≤ 1 - errorUpper * denominatorUpper :=
    RFAP.ConstructiveFraction.sub_nonneg_direct upperProductLeOne
  have complementOrder :
      1 - errorUpper * denominatorUpper ≤
        1 - errorLower * denominatorLower :=
    RFAP.ConstructiveFraction.sub_le_sub_left_direct productOrder 1
  have secondCoordinateNonnegative :
      (0 : Coordinate) ≤
        half ^ 2 * (1 - errorUpper * denominatorUpper) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct halfSquareNonnegative
      upperComplementNonnegative
  have secondCoordinateOrder :
      half ^ 2 * (1 - errorUpper * denominatorUpper) ≤
        half ^ 2 * (1 - errorLower * denominatorLower) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      complementOrder halfSquareNonnegative
  have secondSquareOrder :
      (half ^ 2 * (1 - errorUpper * denominatorUpper)) ^ 2 ≤
        (half ^ 2 * (1 - errorLower * denominatorLower)) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct secondCoordinateNonnegative
      secondCoordinateOrder 2
  rw [gap_eq, gap_eq]
  exact RFAP.ConstructiveFraction.add_le_add_direct firstSquareOrder
    secondSquareOrder

private theorem twentyFiveNinths_le_four_mul_gap
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter) :
    25 / 9 ≤ 4 * gap errorParameter denominatorParameter := by
  have sumBound :
      errorParameter + denominatorParameter ≤ (2 / 3 : Coordinate) := by
    calc
      errorParameter + denominatorParameter ≤ 1 / 3 + 1 / 3 :=
        RFAP.ConstructiveFraction.add_le_add_direct
          (parameter_le_oneThird errorCertificate)
          (parameter_le_oneThird denominatorCertificate)
      _ = 2 / 3 := by decide
  have firstCoordinateBound :
      (5 / 6 : Coordinate) ≤
        1 - half ^ 2 * (errorParameter + denominatorParameter) := by
    have scaledSum :
        half ^ 2 * (errorParameter + denominatorParameter) ≤
          half ^ 2 * (2 / 3 : Coordinate) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sumBound
        (RFAP.ConstructiveFraction.sq_nonneg_direct half)
    calc
      (5 / 6 : Coordinate) = 1 - half ^ 2 * (2 / 3 : Coordinate) := by
        rw [half_sq]
        decide
      _ ≤ 1 - half ^ 2 * (errorParameter + denominatorParameter) :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct scaledSum 1
  have squareBound :
      (5 / 6 : Coordinate) ^ 2 ≤
        (1 - half ^ 2 *
          (errorParameter + denominatorParameter)) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct (by decide)
      firstCoordinateBound 2
  rw [gap_eq]
  calc
    (25 / 9 : Coordinate) = 4 * (5 / 6 : Coordinate) ^ 2 := by decide
    _ ≤ 4 *
        (1 - half ^ 2 *
          (errorParameter + denominatorParameter)) ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        squareBound (by decide)
    _ ≤ 4 *
        ((1 - half ^ 2 *
            (errorParameter + denominatorParameter)) ^ 2 +
          (half ^ 2 *
            (1 - errorParameter * denominatorParameter)) ^ 2) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · exact le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      · decide

theorem error_margin
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter) :
    2 * (1 + RFAP.ConstructiveGaussian.Gaussian.normSq
        (errorRatio errorParameter)) <
      4 * gap errorParameter denominatorParameter := by
  exact (coordinateNorm_le_twentyThreeEighteenths errorCertificate).trans_lt
    ((show (23 / 9 : Coordinate) < 25 / 9 by decide).trans_le
      (twentyFiveNinths_le_four_mul_gap errorCertificate
        denominatorCertificate))

theorem denominator_margin
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter) :
    2 * (1 + RFAP.ConstructiveGaussian.Gaussian.normSq
        (denominatorRatio denominatorParameter)) <
      4 * gap errorParameter denominatorParameter := by
  exact
    (coordinateNorm_denominator_le_twentyThreeEighteenths
      denominatorCertificate).trans_lt
      ((show (23 / 9 : Coordinate) < 25 / 9 by decide).trans_le
        (twentyFiveNinths_le_four_mul_gap errorCertificate
          denominatorCertificate))

theorem gap_pos
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter) :
    0 < gap errorParameter denominatorParameter := by
  have onePlusPositive :
      (0 : Coordinate) <
        1 + RFAP.ConstructiveGaussian.Gaussian.normSq
          (errorRatio errorParameter) :=
    (show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _))
  have scaledPositive :
      0 < 4 * gap errorParameter denominatorParameter :=
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      onePlusPositive).trans
        (error_margin errorCertificate denominatorCertificate)
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct (c := 4)
  · calc
      (0 : Coordinate) * 4 = 0 := by ring1
      _ < 4 * gap errorParameter denominatorParameter := scaledPositive
      _ = gap errorParameter denominatorParameter * 4 := by ring1
  · decide

private theorem left_gap_identity
    (errorParameter denominatorParameter : Coordinate)
    (left right : GaussianInt) :
    toGaussian left * gapVector errorParameter denominatorParameter =
      normalizedError errorParameter left right -
        normalizedDenominator denominatorParameter left right *
          errorRatio errorParameter := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [gapVector, normalizedError, normalizedDenominator,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
    ring1

private theorem right_gap_identity
    (errorParameter denominatorParameter : Coordinate)
    (left right : GaussianInt) :
    toGaussian right * gapVector errorParameter denominatorParameter =
      normalizedDenominator denominatorParameter left right -
        denominatorRatio denominatorParameter *
          normalizedError errorParameter left right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [gapVector, normalizedError, normalizedDenominator,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
    ring1

private theorem coefficient_normNat_lt_four
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    (left right : GaussianInt)
    (errorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedError errorParameter left right) ≤ 1)
    (denominatorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) ≤ 1) :
    normNat left < 4 ∧ normNat right < 4 := by
  have errorNormNonnegative :
      (0 : Coordinate) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (errorRatio errorParameter) :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have denominatorNormNonnegative :
      (0 : Coordinate) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (denominatorRatio denominatorParameter) :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have denominatorScaledLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (errorRatio errorParameter) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (errorRatio errorParameter) := by
    calc
      _ ≤ (1 : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (errorRatio errorParameter) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          denominatorBound errorNormNonnegative
      _ = _ := by ring1
  have errorScaledLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError errorParameter left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (denominatorRatio denominatorParameter) := by
    calc
      _ ≤ (1 : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          errorBound denominatorNormNonnegative
      _ = _ := by ring1
  have leftSumBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError errorParameter left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right *
              errorRatio errorParameter) ≤
        1 + RFAP.ConstructiveGaussian.Gaussian.normSq
          (errorRatio errorParameter) := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    exact RFAP.ConstructiveFraction.add_le_add_direct
      errorBound denominatorScaledLe
  have rightSumBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter *
              normalizedError errorParameter left right) ≤
        1 + RFAP.ConstructiveGaussian.Gaussian.normSq
          (denominatorRatio denominatorParameter) := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    apply RFAP.ConstructiveFraction.add_le_add_direct denominatorBound
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError errorParameter left right) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError errorParameter left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter) := by ring1
      _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq
          (denominatorRatio denominatorParameter) := errorScaledLe
  have leftProductStrict :
      (normNat left : Coordinate) * gap errorParameter denominatorParameter <
        4 * gap errorParameter denominatorParameter := by
    calc
      (normNat left : Coordinate) *
          gap errorParameter denominatorParameter =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian left *
            gapVector errorParameter denominatorParameter) := by
        unfold gap
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
          normSq_toGaussian]
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right -
            normalizedDenominator denominatorParameter left right *
              errorRatio errorParameter) := by
        rw [left_gap_identity]
      _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedError errorParameter left right) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator denominatorParameter left right *
                errorRatio errorParameter)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + RFAP.ConstructiveGaussian.Gaussian.normSq
            (errorRatio errorParameter)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ < 4 * gap errorParameter denominatorParameter :=
        error_margin errorCertificate denominatorCertificate
  have rightProductStrict :
      (normNat right : Coordinate) * gap errorParameter denominatorParameter <
        4 * gap errorParameter denominatorParameter := by
    calc
      (normNat right : Coordinate) *
          gap errorParameter denominatorParameter =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian right *
            gapVector errorParameter denominatorParameter) := by
        unfold gap
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
          normSq_toGaussian]
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedDenominator denominatorParameter left right -
            denominatorRatio denominatorParameter *
              normalizedError errorParameter left right) := by
        rw [right_gap_identity]
      _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator denominatorParameter left right) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (denominatorRatio denominatorParameter *
                normalizedError errorParameter left right)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ < 4 * gap errorParameter denominatorParameter :=
        denominator_margin errorCertificate denominatorCertificate
  refine ⟨?_, ?_⟩
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      leftProductStrict (gap_pos errorCertificate denominatorCertificate)
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      rightProductStrict (gap_pos errorCertificate denominatorCertificate)

private theorem normSq_denominatorRatio_lt_one
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (denominatorRatio value) < 1 := by
  rw [normSq_denominatorRatio]
  simpa only [normSq_errorRatio] using
    normSq_errorRatio_lt_one certificate

/-- A coarse but finite robust cutoff: if the exact-source normalized error
quadrance is at most five and the normalized denominator remains inside its
unit wall, both Gaussian-integral coefficients lie in quadrance `< 32`. -/
theorem coefficient_normNat_lt_thirtyTwo
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    (left right : GaussianInt)
    (errorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedError errorParameter left right) ≤ 5)
    (denominatorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) ≤ 1) :
    normNat left < 32 ∧ normNat right < 32 := by
  have errorRatioBound :=
    (normSq_errorRatio_lt_one errorCertificate).le
  have denominatorRatioBound :=
    (normSq_denominatorRatio_lt_one denominatorCertificate).le
  have errorRatioNonnegative :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg
      (errorRatio errorParameter)
  have denominatorRatioNonnegative :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg
      (denominatorRatio denominatorParameter)
  have denominatorScaledLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (errorRatio errorParameter) ≤ 1 := by
    calc
      _ ≤ (1 : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (errorRatio errorParameter) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          denominatorBound errorRatioNonnegative
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (errorRatio errorParameter) := by ring1
      _ ≤ 1 := errorRatioBound
  have errorScaledLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError errorParameter left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter) ≤ 5 := by
    calc
      _ ≤ (5 : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          errorBound denominatorRatioNonnegative
      _ ≤ 5 * (1 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorRatioBound (by decide)
      _ = 5 := by ring1
  have leftSumBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError errorParameter left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right *
              errorRatio errorParameter) ≤ 6 := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    calc
      _ ≤ (5 : Coordinate) + 1 :=
        RFAP.ConstructiveFraction.add_le_add_direct errorBound
          denominatorScaledLe
      _ = 6 := by ring1
  have rightSumBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio denominatorParameter *
              normalizedError errorParameter left right) ≤ 6 := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (denominatorRatio denominatorParameter) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedError errorParameter left right) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedError errorParameter left right) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (denominatorRatio denominatorParameter) := by ring1
      _ ≤ (1 : Coordinate) + 5 :=
        RFAP.ConstructiveFraction.add_le_add_direct denominatorBound
          errorScaledLe
      _ = 6 := by ring1
  have thirtyTwoGapLower :
      (16 : Coordinate) ≤
        32 * gap errorParameter denominatorParameter := by
    have twoLeFourGap :
        (2 : Coordinate) ≤ 4 * gap errorParameter denominatorParameter :=
      (show (2 : Coordinate) ≤ 25 / 9 by decide).trans
        (twentyFiveNinths_le_four_mul_gap errorCertificate
          denominatorCertificate)
    calc
      (16 : Coordinate) = 8 * 2 := by ring1
      _ ≤ 8 * (4 * gap errorParameter denominatorParameter) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          twoLeFourGap (by decide)
      _ = 32 * gap errorParameter denominatorParameter := by ring1
  have leftProductStrict :
      (normNat left : Coordinate) *
          gap errorParameter denominatorParameter <
        32 * gap errorParameter denominatorParameter := by
    calc
      (normNat left : Coordinate) *
          gap errorParameter denominatorParameter =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian left *
            gapVector errorParameter denominatorParameter) := by
        unfold gap
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
          normSq_toGaussian]
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right -
            normalizedDenominator denominatorParameter left right *
              errorRatio errorParameter) := by
        rw [left_gap_identity]
      _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedError errorParameter left right) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator denominatorParameter left right *
                errorRatio errorParameter)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 * (6 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ = 12 := by ring1
      _ < 16 := by decide
      _ ≤ 32 * gap errorParameter denominatorParameter := thirtyTwoGapLower
  have rightProductStrict :
      (normNat right : Coordinate) *
          gap errorParameter denominatorParameter <
        32 * gap errorParameter denominatorParameter := by
    calc
      (normNat right : Coordinate) *
          gap errorParameter denominatorParameter =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian right *
            gapVector errorParameter denominatorParameter) := by
        unfold gap
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
          normSq_toGaussian]
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedDenominator denominatorParameter left right -
            denominatorRatio denominatorParameter *
              normalizedError errorParameter left right) := by
        rw [right_gap_identity]
      _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator denominatorParameter left right) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (denominatorRatio denominatorParameter *
                normalizedError errorParameter left right)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 * (6 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ = 12 := by ring1
      _ < 16 := by decide
      _ ≤ 32 * gap errorParameter denominatorParameter := thirtyTwoGapLower
  refine ⟨?_, ?_⟩
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      leftProductStrict (gap_pos errorCertificate denominatorCertificate)
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      rightProductStrict (gap_pos errorCertificate denominatorCertificate)

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

private theorem two_mul_half : (2 : Coordinate) * half = 1 := by
  unfold half
  decide

private theorem two_mul_error_real
    (left right : GaussianInt) (value : Coordinate) :
    2 * (normalizedError value left right).re =
      scaledErrorReal left right value := by
  simp only [normalizedError, errorRatio,
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
    2 * (normalizedError value left right).im =
      scaledErrorImaginary left right value := by
  simp only [normalizedError, errorRatio,
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
    2 * (normalizedDenominator value left right).re =
      scaledDenominatorReal left right value := by
  simp only [normalizedDenominator, denominatorRatio,
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
    2 * (normalizedDenominator value left right).im =
      scaledDenominatorImaginary left right value := by
  simp only [normalizedDenominator, denominatorRatio,
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
    (RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedError value left right) - 1) * 4 =
      scaledErrorReal left right value ^ 2 +
        scaledErrorImaginary left right value ^ 2 - 4 := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  calc
    (((normalizedError value left right).re ^ 2 +
          (normalizedError value left right).im ^ 2) - 1) * 4 =
      (2 * (normalizedError value left right).re) ^ 2 +
        (2 * (normalizedError value left right).im) ^ 2 - 4 := by ring1
    _ = scaledErrorReal left right value ^ 2 +
        scaledErrorImaginary left right value ^ 2 - 4 := by
      rw [two_mul_error_real, two_mul_error_imaginary]

private theorem denominator_difference_mul_four
    (left right : GaussianInt) (value : Coordinate) :
    (RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator value left right) - 1) * 4 =
      scaledDenominatorReal left right value ^ 2 +
        scaledDenominatorImaginary left right value ^ 2 - 4 := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  calc
    (((normalizedDenominator value left right).re ^ 2 +
          (normalizedDenominator value left right).im ^ 2) - 1) * 4 =
      (2 * (normalizedDenominator value left right).re) ^ 2 +
        (2 * (normalizedDenominator value left right).im) ^ 2 - 4 := by
      ring1
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

private theorem templatePlus_pos
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 < 1 + 4 * value + value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + value ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (parameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.sq_nonneg_direct value)
  exact (show (0 : Coordinate) < 1 by decide).trans_le
    (by
      calc
        (1 : Coordinate) ≤ 1 + (4 * value + value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 1 + 4 * value + value ^ 2 := by ring1)

private theorem templateFive_pos {value : Coordinate} :
    0 < 5 + value ^ 2 :=
  (show (0 : Coordinate) < 5 by decide).trans_le
    (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct value))

private theorem templateSixPlusFour_pos
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 < 6 + 4 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 4 * value + 2 * value ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (parameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct value))
  exact (show (0 : Coordinate) < 6 by decide).trans_le
    (by
      calc
        (6 : Coordinate) ≤ 6 + (4 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 4 * value + 2 * value ^ 2 := by ring1)

private theorem templateNineMinusFour_pos
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 < 9 - 4 * value + value ^ 2 := by
  calc
    (0 : Coordinate) <
        8 + RFAP.FiniteWindowSharpness.parameterPolynomial value :=
      (show (0 : Coordinate) < 8 by decide).trans_le
        (le_add_of_nonneg_right certificate.2.2.le)
    _ = 9 - 4 * value + value ^ 2 := by
      unfold RFAP.FiniteWindowSharpness.parameterPolynomial
      ring1

private theorem templateFourteen_pos {value : Coordinate} :
    0 < 14 + 2 * value ^ 2 :=
  (show (0 : Coordinate) < 14 by decide).trans_le
    (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct value)))

private theorem templateSixMinusEight_pos
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 < 6 - 8 * value + 2 * value ^ 2 := by
  have doubledNonnegative :
      0 ≤ 2 * RFAP.FiniteWindowSharpness.parameterPolynomial value :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      certificate.2.2.le
  calc
    (0 : Coordinate) <
        4 + 2 * RFAP.FiniteWindowSharpness.parameterPolynomial value :=
      (show (0 : Coordinate) < 4 by decide).trans_le
        (le_add_of_nonneg_right doubledNonnegative)
    _ = 6 - 8 * value + 2 * value ^ 2 := by
      unfold RFAP.FiniteWindowSharpness.parameterPolynomial
      ring1

private theorem templateSixPlusEight_pos
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 < 6 + 8 * value + 2 * value ^ 2 := by
  have tailNonnegative : 0 ≤ 8 * value + 2 * value ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (parameter_nonnegative certificate))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct value))
  exact (show (0 : Coordinate) < 6 by decide).trans_le
    (by
      calc
        (6 : Coordinate) ≤ 6 + (8 * value + 2 * value ^ 2) :=
          le_add_of_nonneg_right tailNonnegative
        _ = 6 + 8 * value + 2 * value ^ 2 := by ring1)

private theorem templateMinus_pos
    {value : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter value) :
    0 < 1 - 4 * value + value ^ 2 := by
  calc
    (0 : Coordinate) <
        RFAP.FiniteWindowSharpness.parameterPolynomial value :=
      certificate.2.2
    _ = 1 - 4 * value + value ^ 2 := by
      unfold RFAP.FiniteWindowSharpness.parameterPolynomial
      ring1

macro "scaled_ring" : tactic =>
  `(tactic| (simp [scaledErrorReal, scaledErrorImaginary,
      scaledDenominatorReal, scaledDenominatorImaginary, toGaussian,
      RFAP.HurwitzGeometry.imaginaryUnit] <;> ring1))

macro "solve_two_parameter_exterior"
    errorCertificate:term "," errorParameter:term ","
    denominatorCertificate:term "," denominatorParameter:term : tactic =>
  `(tactic| first
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateMinus_pos $errorCertificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateMinus_pos $denominatorCertificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templatePlus_pos $errorCertificate using 1 <;> scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templatePlus_pos $denominatorCertificate using 1 <;> scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateFive_pos (value := $errorParameter) using 1 <;>
        scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateFive_pos (value := $denominatorParameter) using 1 <;>
        scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateSixPlusFour_pos $errorCertificate using 1 <;>
        scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateSixPlusFour_pos $denominatorCertificate using 1 <;>
        scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateNineMinusFour_pos $errorCertificate using 1 <;>
        scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateNineMinusFour_pos $denominatorCertificate using 1 <;>
        scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateFourteen_pos (value := $errorParameter) using 1 <;>
        scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateFourteen_pos (value := $denominatorParameter) using 1 <;>
        scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateSixMinusEight_pos $errorCertificate using 1 <;>
        scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateSixMinusEight_pos $denominatorCertificate using 1 <;>
        scaled_ring
    | left
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [error_difference_mul_four]
      convert templateSixPlusEight_pos $errorCertificate using 1 <;>
        scaled_ring
    | right
      apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      apply positive_of_mul_four_positive
      rw [denominator_difference_mul_four]
      convert templateSixPlusEight_pos $denominatorCertificate using 1 <;>
        scaled_ring)

private theorem unit_unit_strictly_exterior
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftUnit : RFAP.HurwitzGeometry.IsGaussianUnit left)
    (rightUnit : RFAP.HurwitzGeometry.IsGaussianUnit right) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl <;>
    rcases rightUnit with rfl | rfl | rfl | rfl <;>
      solve_two_parameter_exterior errorCertificate, errorParameter,
        denominatorCertificate, denominatorParameter

private theorem unit_diagonal_strictly_exterior
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftUnit : RFAP.HurwitzGeometry.IsGaussianUnit left)
    (rightDiagonal : RFAP.HurwitzGeometry.IsDiagonal right) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) := by
  rcases leftUnit with rfl | rfl | rfl | rfl <;>
    rcases rightDiagonal with rfl | rfl | rfl | rfl <;>
      solve_two_parameter_exterior errorCertificate, errorParameter,
        denominatorCertificate, denominatorParameter

private theorem diagonal_unit_strictly_exterior
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftDiagonal : RFAP.HurwitzGeometry.IsDiagonal left)
    (rightUnit : RFAP.HurwitzGeometry.IsGaussianUnit right) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
    rcases rightUnit with rfl | rfl | rfl | rfl <;>
      solve_two_parameter_exterior errorCertificate, errorParameter,
        denominatorCertificate, denominatorParameter

private theorem diagonal_diagonal_strictly_exterior
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    {left right : GaussianInt}
    (leftDiagonal : RFAP.HurwitzGeometry.IsDiagonal left)
    (rightDiagonal : RFAP.HurwitzGeometry.IsDiagonal right) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
    rcases rightDiagonal with rfl | rfl | rfl | rfl <;>
      solve_two_parameter_exterior errorCertificate, errorParameter,
        denominatorCertificate, denominatorParameter

private theorem small_nonzero_strictly_exterior
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) (leftSmall : normNat left < 4)
    (rightSmall : normNat right < 4) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) := by
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
    · exact unit_unit_strictly_exterior errorCertificate
        denominatorCertificate leftUnit rightUnit
    · exact unit_diagonal_strictly_exterior errorCertificate
        denominatorCertificate leftUnit rightDiagonal
  · rcases rightShape with rightUnit | rightDiagonal
    · exact diagonal_unit_strictly_exterior errorCertificate
        denominatorCertificate leftDiagonal rightUnit
    · exact diagonal_diagonal_strictly_exterior errorCertificate
        denominatorCertificate leftDiagonal rightDiagonal

/-- Uniform two-parameter exterior theorem for every pair of rational
parameters in the finite critical chamber. -/
theorem strictExterior
    {errorParameter denominatorParameter : Coordinate}
    (errorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter errorParameter)
    (denominatorCertificate :
      RFAP.FiniteWindowSharpness.IsFiniteCriticalParameter
        denominatorParameter)
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator denominatorParameter left right) := by
  by_cases errorExterior :
      (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError errorParameter left right)
  · exact Or.inl errorExterior
  · by_cases denominatorExterior :
        (1 : Coordinate) <
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator denominatorParameter left right)
    · exact Or.inr denominatorExterior
    · have small := coefficient_normNat_lt_four errorCertificate
        denominatorCertificate left right (le_of_not_gt errorExterior)
        (le_of_not_gt denominatorExterior)
      exact small_nonzero_strictly_exterior errorCertificate
        denominatorCertificate left right leftNonzero rightNonzero
        small.1 small.2

end RFAP.TwoParameterCylinder
