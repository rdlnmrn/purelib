import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.BasisCylinder
import RFAP.Approximation.CriticalBranch

/-!
# A two-window feasibility certificate on the critical Pell branch

This module checks the first genuinely same-source transition.  The source
constructed for Pell stage one supports both its native critical window and
the next Pell pair basis at stage two.  The second proof uses only an exact
small-coefficient cylinder calculation at rational parameters `1/4` and
`15/56`; no global best-pair enumeration is evaluated.
-/

namespace RFAP.CriticalTwoWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

private def oneHalf : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨1, 2, by decide⟩

private def oneEighth : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨1, 8, by decide⟩

private def fifteenOverOneHundredTwelve : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨15, 112, by decide⟩

private def fifteenOverFiftySix : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨15, 56, by decide⟩

private theorem fifteenOverFiftySix_mul_denominator :
    fifteenOverFiftySix * 56 = 15 := by
  unfold fifteenOverFiftySix
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 15, den := 56, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

private def fourOverFifteen : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨4, 15, by decide⟩

private def twoOverFifteen : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨2, 15, by decide⟩

private def errorRatio : Gaussian :=
  ⟨oneHalf, oneEighth⟩

private def denominatorRatio : Gaussian :=
  ⟨fifteenOverOneHundredTwelve, -oneHalf⟩

private def normalizedError
    (left right : GaussianInt) : Gaussian :=
  toGaussian left + toGaussian right * errorRatio

private def normalizedDenominator
    (left right : GaussianInt) : Gaussian :=
  toGaussian left * denominatorRatio + toGaussian right

private def gapVector : Gaussian := 1 - denominatorRatio * errorRatio

private def gap : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq gapVector

private theorem gap_pos : 0 < gap := by decide

private theorem error_margin :
    2 * (1 + RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio) <
      4 * gap := by
  decide

private theorem denominator_margin :
    2 * (1 + RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio) <
      4 * gap := by
  decide

private theorem left_gap_identity
    (left right : GaussianInt) :
    toGaussian left * gapVector =
      normalizedError left right -
        normalizedDenominator left right * errorRatio := by
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
    (left right : GaussianInt) :
    toGaussian right * gapVector =
      normalizedDenominator left right -
        denominatorRatio * normalizedError left right := by
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
    (left right : GaussianInt)
    (errorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedError left right) ≤ 1)
    (denominatorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator left right) ≤ 1) :
    normNat left < 4 ∧ normNat right < 4 := by
  have errorNormNonnegative :
      (0 : Coordinate) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have denominatorNormNonnegative :
      (0 : Coordinate) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have denominatorScaledLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio := by
    calc
      _ ≤ (1 : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          denominatorBound errorNormNonnegative
      _ = _ := by ring1
  have errorScaledLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio := by
    calc
      _ ≤ (1 : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          errorBound denominatorNormNonnegative
      _ = _ := by ring1
  have leftSumBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator left right * errorRatio) ≤
        1 + RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    exact RFAP.ConstructiveFraction.add_le_add_direct
      errorBound denominatorScaledLe
  have rightSumBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator left right) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominatorRatio * normalizedError left right) ≤
        1 + RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    apply RFAP.ConstructiveFraction.add_le_add_direct denominatorBound
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError left right) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedError left right) *
          RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio := by
        ring1
      _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio :=
        errorScaledLe
  have leftProductStrict :
      (normNat left : Coordinate) * gap < 4 * gap := by
    calc
      (normNat left : Coordinate) * gap =
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian left * gapVector) := by
        unfold gap
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
          normSq_toGaussian]
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError left right -
            normalizedDenominator left right * errorRatio) := by
        rw [left_gap_identity]
      _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedError left right) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator left right * errorRatio)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ < 4 * gap := error_margin
  have rightProductStrict :
      (normNat right : Coordinate) * gap < 4 * gap := by
    calc
      (normNat right : Coordinate) * gap =
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian right * gapVector) := by
        unfold gap
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
          normSq_toGaussian]
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedDenominator left right -
            denominatorRatio * normalizedError left right) := by
        rw [right_gap_identity]
      _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator left right) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (denominatorRatio * normalizedError left right)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + RFAP.ConstructiveGaussian.Gaussian.normSq denominatorRatio) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ < 4 * gap := denominator_margin
  constructor
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      leftProductStrict gap_pos
  · apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      rightProductStrict gap_pos

private theorem small_nonzero_strictly_exterior
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) (leftSmall : normNat left < 4)
    (rightSmall : normNat right < 4) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator left right) := by
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
    · rcases leftUnit with rfl | rfl | rfl | rfl <;>
        rcases rightUnit with rfl | rfl | rfl | rfl <;> decide
    · rcases leftUnit with rfl | rfl | rfl | rfl <;>
        rcases rightDiagonal with rfl | rfl | rfl | rfl <;> decide
  · rcases rightShape with rightUnit | rightDiagonal
    · rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
        rcases rightUnit with rfl | rfl | rfl | rfl <;> decide
    · rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
        rcases rightDiagonal with rfl | rfl | rfl | rfl <;> decide

/-- The transformed stage-two basis has an exact strict normalized exterior
certificate at the stage-one source parameters. -/
theorem normalized_strictExterior
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) :
    (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError left right) ∨
      1 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (normalizedDenominator left right) := by
  by_cases errorExterior :
      (1 : Coordinate) <
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (normalizedError left right)
  · exact Or.inl errorExterior
  · by_cases denominatorExterior :
        (1 : Coordinate) <
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (normalizedDenominator left right)
    · exact Or.inr denominatorExterior
    · have small := coefficient_normNat_lt_four left right
        (le_of_not_gt errorExterior) (le_of_not_gt denominatorExterior)
      exact small_nonzero_strictly_exterior left right leftNonzero
        rightNonzero small.1 small.2

private theorem pellParameter_one :
    RFAP.FiniteWindowSharpness.pellParameter 1 = fourOverFifteen := by
  decide

private theorem criticalErrorRatio_one :
    RFAP.FiniteWindowSharpness.criticalErrorRatio
        (RFAP.FiniteWindowSharpness.pellParameter 1) =
      ⟨oneHalf, twoOverFifteen⟩ := by
  rw [pellParameter_one]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private def lowerErrorScale : Gaussian := ⟨fourOverFifteen, 0⟩

private theorem lowerCombinationFactor :
    toGaussian RFAP.CriticalBranch.lowerFromLower +
        toGaussian RFAP.CriticalBranch.lowerFromUpper *
          (⟨oneHalf, twoOverFifteen⟩ : Gaussian) =
      lowerErrorScale := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private theorem upperCombinationFactor :
    toGaussian RFAP.CriticalBranch.upperFromLower +
        toGaussian RFAP.CriticalBranch.upperFromUpper *
          (⟨oneHalf, twoOverFifteen⟩ : Gaussian) =
      lowerErrorScale * errorRatio := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private theorem stageTwo_error_lower :
    RFAP.HurwitzApproximation.error
        (RFAP.FiniteWindowSharpness.criticalSource 1).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair 2) =
      RFAP.FiniteWindowSharpness.criticalLowerError 1 * lowerErrorScale := by
  rw [show (2 : Nat) = 1 + 1 by rfl,
    RFAP.CriticalBranch.criticalLowerPair_succ,
    error_linearCombination,
    RFAP.FiniteWindowSharpness.criticalSource_error_lower,
    RFAP.FiniteWindowSharpness.criticalSource_error_upper,
    criticalErrorRatio_one]
  calc
    toGaussian RFAP.CriticalBranch.lowerFromLower *
          RFAP.FiniteWindowSharpness.criticalLowerError 1 +
        toGaussian RFAP.CriticalBranch.lowerFromUpper *
          (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
            (⟨oneHalf, twoOverFifteen⟩ : Gaussian)) =
      RFAP.FiniteWindowSharpness.criticalLowerError 1 *
        (toGaussian RFAP.CriticalBranch.lowerFromLower +
          toGaussian RFAP.CriticalBranch.lowerFromUpper *
            (⟨oneHalf, twoOverFifteen⟩ : Gaussian)) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = RFAP.FiniteWindowSharpness.criticalLowerError 1 *
        lowerErrorScale := by rw [lowerCombinationFactor]

private theorem stageTwo_error_upper :
    RFAP.HurwitzApproximation.error
        (RFAP.FiniteWindowSharpness.criticalSource 1).value
        (RFAP.FiniteWindowSharpness.criticalUpperPair 2) =
      (RFAP.FiniteWindowSharpness.criticalLowerError 1 * lowerErrorScale) *
        errorRatio := by
  rw [show (2 : Nat) = 1 + 1 by rfl,
    RFAP.CriticalBranch.criticalUpperPair_succ,
    error_linearCombination,
    RFAP.FiniteWindowSharpness.criticalSource_error_lower,
    RFAP.FiniteWindowSharpness.criticalSource_error_upper,
    criticalErrorRatio_one]
  calc
    toGaussian RFAP.CriticalBranch.upperFromLower *
          RFAP.FiniteWindowSharpness.criticalLowerError 1 +
        toGaussian RFAP.CriticalBranch.upperFromUpper *
          (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
            (⟨oneHalf, twoOverFifteen⟩ : Gaussian)) =
      RFAP.FiniteWindowSharpness.criticalLowerError 1 *
        (toGaussian RFAP.CriticalBranch.upperFromLower +
          toGaussian RFAP.CriticalBranch.upperFromUpper *
            (⟨oneHalf, twoOverFifteen⟩ : Gaussian)) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = RFAP.FiniteWindowSharpness.criticalLowerError 1 *
        (lowerErrorScale * errorRatio) := by rw [upperCombinationFactor]
    _ = (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
          lowerErrorScale) * errorRatio := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

private theorem stageTwo_denominator_lower :
    toGaussian
        (RFAP.FiniteWindowSharpness.criticalLowerPair 2).denominator =
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator *
        denominatorRatio := by
  have parameterTwo :
      RFAP.FiniteWindowSharpness.pellParameter 2 =
        fifteenOverFiftySix := by
    have fiftySixPositive : (0 : Coordinate) < (56 : Coordinate) :=
      RFAP.ConstructiveFraction.natCast_pos_direct (by decide)
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (c := (56 : Coordinate)) fiftySixPositive.ne'
    calc
      RFAP.FiniteWindowSharpness.pellParameter 2 * (56 : Coordinate) =
          (15 : Coordinate) := by
        unfold RFAP.FiniteWindowSharpness.pellParameter
        rw [show RFAP.FiniteWindowSharpness.pellNumerator 2 = 15 by decide,
          show RFAP.FiniteWindowSharpness.pellDenominator 2 = 56 by decide]
        exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          fiftySixPositive.ne'
      _ = fifteenOverFiftySix * (56 : Coordinate) :=
        fifteenOverFiftySix_mul_denominator.symm
  have ratioTwo :
      RFAP.FiniteWindowSharpness.criticalDenominatorRatio
          (RFAP.FiniteWindowSharpness.pellParameter 2) =
        denominatorRatio := by
    rw [parameterTwo]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  have upperNonzero :
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator ≠ 0 := by
    intro zero
    exact RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero 2
      (toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    RFAP.FiniteWindowSharpness.criticalPair_denominatorRatio 2
  rw [ratioTwo] at ratioIdentity
  calc
    toGaussian
          (RFAP.FiniteWindowSharpness.criticalLowerPair 2).denominator =
        RFAP.DirichletWindow.denominatorRatio
            (RFAP.FiniteWindowSharpness.criticalLowerPair 2)
            (RFAP.FiniteWindowSharpness.criticalUpperPair 2) *
          toGaussian
            (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator := by
      unfold RFAP.DirichletWindow.denominatorRatio
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ upperNonzero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = denominatorRatio *
          toGaussian
            (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator := by
      rw [ratioIdentity]
    _ = toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator *
        denominatorRatio := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]

private theorem stageTwo_error_linearCombination
    (left right : GaussianInt) :
    RFAP.HurwitzApproximation.error
        (RFAP.FiniteWindowSharpness.criticalSource 1).value
        (linearCombination
          (RFAP.FiniteWindowSharpness.criticalLowerPair 2)
          (RFAP.FiniteWindowSharpness.criticalUpperPair 2) left right) =
      (RFAP.FiniteWindowSharpness.criticalLowerError 1 * lowerErrorScale) *
        normalizedError left right := by
  rw [error_linearCombination, stageTwo_error_lower,
    stageTwo_error_upper]
  unfold normalizedError
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem stageTwo_denominator_linearCombination
    (left right : GaussianInt) :
    toGaussian
        (linearCombination
          (RFAP.FiniteWindowSharpness.criticalLowerPair 2)
          (RFAP.FiniteWindowSharpness.criticalUpperPair 2)
          left right).denominator =
      toGaussian
          (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator *
        normalizedDenominator left right := by
  simp only [linearCombination, toGaussian_add, toGaussian_mul]
  rw [stageTwo_denominator_lower]
  unfold normalizedDenominator
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem stageTwo_lowerError_normSq_pos :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
        lowerErrorScale) := by
  have firstWindow :=
    RFAP.FiniteWindowSharpness.criticalPairs_areConsecutiveBest 1
  have nativeErrorOrder :
      errorQuadrance
          (RFAP.FiniteWindowSharpness.criticalSource 1).value
          (RFAP.FiniteWindowSharpness.criticalUpperPair 1) <
        errorQuadrance
          (RFAP.FiniteWindowSharpness.criticalSource 1).value
          (RFAP.FiniteWindowSharpness.criticalLowerPair 1) :=
    firstWindow.2.1.2.1 _ firstWindow.1.1 firstWindow.2.2.1
  have oldLowerPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.FiniteWindowSharpness.criticalLowerError 1) := by
    rw [← RFAP.FiniteWindowSharpness.criticalSource_error_lower]
    exact (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _).trans_lt
      nativeErrorOrder
  have scalePositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq lowerErrorScale := by
    decide
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
  exact RFAP.ConstructiveFraction.mul_pos_direct oldLowerPositive scalePositive

private theorem stageTwo_upperDenominator_normSq_pos :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (toGaussian
        (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator) := by
  apply RFAP.ConstructiveGaussian.Gaussian.normSq_pos
  intro zero
  exact RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero 2
    (toGaussian_eq_zero.mp zero)

/-- The exact strict-basis certificate for the second window at the fixed
stage-one rational source. -/
theorem stageTwoStrictExteriorCertificate :
    RFAP.BasisCylinder.StrictExteriorCertificate
      (RFAP.FiniteWindowSharpness.criticalSource 1).value
      (RFAP.FiniteWindowSharpness.criticalLowerPair 2)
      (RFAP.FiniteWindowSharpness.criticalUpperPair 2) := by
  refine
    { indexOne := RFAP.FiniteWindowSharpness.criticalPair_indexOne 2
      lowerDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalLower_denominator_ne_zero 2
      upperDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero 2
      errorOrder := ?_
      denominatorOrder :=
        RFAP.FiniteWindowSharpness.critical_denominatorQuadrance_ordered 2
      bothNonzeroExterior := ?_ }
  · unfold errorQuadrance
    rw [stageTwo_error_lower, stageTwo_error_upper]
    have ratioStrict :
        RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio < 1 := by
      decide
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.FiniteWindowSharpness.criticalLowerError 1 *
            lowerErrorScale) * errorRatio) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
              lowerErrorScale) *
          RFAP.ConstructiveGaussian.Gaussian.normSq errorRatio := by
        rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
      _ < RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
              lowerErrorScale) * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          stageTwo_lowerError_normSq_pos ratioStrict
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
            lowerErrorScale) := by ring1
  · intro left right leftNonzero rightNonzero
    rcases normalized_strictExterior left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold errorQuadrance
      rw [stageTwo_error_lower, stageTwo_error_linearCombination]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
              lowerErrorScale) =
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
                lowerErrorScale) * 1 := by ring1
        _ < RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
                lowerErrorScale) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedError left right) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            stageTwo_lowerError_normSq_pos errorExterior
        _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            ((RFAP.FiniteWindowSharpness.criticalLowerError 1 *
              lowerErrorScale) * normalizedError left right) := by
          exact
            (RFAP.ConstructiveGaussian.Gaussian.normSq_mul
              (RFAP.FiniteWindowSharpness.criticalLowerError 1 *
                lowerErrorScale) (normalizedError left right)).symm
    · right
      apply (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
      unfold denominatorQuadrance
      rw [← normSq_toGaussian, ← normSq_toGaussian,
        stageTwo_denominator_linearCombination]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian
              (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator) =
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator) *
            1 := by ring1
        _ < RFAP.ConstructiveGaussian.Gaussian.normSq
              (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (normalizedDenominator left right) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            stageTwo_upperDenominator_normSq_pos denominatorExterior
        _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            (toGaussian
                (RFAP.FiniteWindowSharpness.criticalUpperPair 2).denominator *
              normalizedDenominator left right) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul]

/-- The next Pell pair basis is a genuine consecutive-best window for the
same rational source as the preceding stage-one window. -/
theorem stageTwo_areConsecutiveBest_at_stageOneSource :
    AreConsecutiveBest
      (RFAP.FiniteWindowSharpness.criticalSource 1).value
      (RFAP.FiniteWindowSharpness.criticalLowerPair 2)
      (RFAP.FiniteWindowSharpness.criticalUpperPair 2) :=
  stageTwoStrictExteriorCertificate.areConsecutiveBest

/-- Constructive two-window feasibility: one displayed rational source
supports two strictly scale-separated critical Pell windows. -/
theorem criticalSource_one_supports_two_windows :
    AreConsecutiveBest
        (RFAP.FiniteWindowSharpness.criticalSource 1).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair 1)
        (RFAP.FiniteWindowSharpness.criticalUpperPair 1) ∧
      AreConsecutiveBest
        (RFAP.FiniteWindowSharpness.criticalSource 1).value
        (RFAP.FiniteWindowSharpness.criticalLowerPair 2)
        (RFAP.FiniteWindowSharpness.criticalUpperPair 2) ∧
      denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalUpperPair 1) <
        denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalLowerPair 2) :=
  ⟨RFAP.FiniteWindowSharpness.criticalPairs_areConsecutiveBest 1,
    stageTwo_areConsecutiveBest_at_stageOneSource,
    RFAP.CriticalBranch.criticalUpper_lt_nextLower_denominatorQuadrance 1⟩

end RFAP.CriticalTwoWindow
