module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
public import Purelib.NumberTheory.Approximation.Best.Cylinder.Basis
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Transition
import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Pell.FiniteBranch
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# A two-window feasibility certificate on the critical Pell branch

This module checks the first genuinely same-source transition.  The source
constructed for Pell stage one supports both its native critical window and
the next Pell pair basis at stage two.  The second proof uses only an exact
small-coefficient cylinder calculation at rational parameters `1/4` and
`15/56`; no global best-pair enumeration is evaluated.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Initial

/-- The normalized signed fraction representing one half. -/
private def oneHalf : Fraction.Rational :=
  SignedFraction.Normalization.ofFraction ⟨1, 2, by decide⟩

/-- The normalized signed fraction representing one eighth. -/
private def oneEighth : Fraction.Rational
  :=
  SignedFraction.Normalization.ofFraction ⟨1, 8, by decide⟩

/-- The normalized signed fraction representing `15/112`. -/
private def fifteenOverOneHundredTwelve :
  Fraction.Rational :=
  SignedFraction.Normalization.ofFraction ⟨15, 112, by decide⟩

/-- The normalized signed fraction representing `15/56`. -/
private def fifteenOverFiftySix :
  Fraction.Rational :=
  SignedFraction.Normalization.ofFraction ⟨15, 56, by decide⟩

/-- Multiplication by 56 clears the retained `15/56` fraction denominator. -/
private theorem
  fifteenOverFiftySix_mul_denominator :
    fifteenOverFiftySix * 56 = 15 := by
  unfold fifteenOverFiftySix
  have clearance := SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 15, den := 56, den_pos := by decide } :
      SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- The normalized signed fraction representing `4/15`. -/
private def fourOverFifteen :
  Fraction.Rational :=
  SignedFraction.Normalization.ofFraction ⟨4, 15, by decide⟩

/-- The normalized signed fraction representing `2/15`. -/
private def twoOverFifteen :
  Fraction.Rational :=
  SignedFraction.Normalization.ofFraction ⟨2, 15, by decide⟩

/-- The normalized stage-two error ratio `(1/2, 1/8)` at the stage-one source. -/
private def errorRatio :
  Gaussian.Basic.Canonical :=
  ⟨oneHalf, oneEighth⟩

/-- The normalized stage-two denominator ratio `(15/112, -1/2)`. -/
private def denominatorRatio :
  Gaussian.Basic.Canonical :=
  ⟨fifteenOverOneHundredTwelve, -oneHalf⟩

/-- The error coordinate of an integral coefficient pair in the normalized stage-two basis. -/
private def normalizedError
    (left right : GaussianInt) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian left + GaussianInt.toGaussian right * errorRatio

/-- The denominator coordinate of an integral coefficient pair in the normalized stage-two basis. -/
private def normalizedDenominator
    (left right : GaussianInt) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian left * denominatorRatio + GaussianInt.toGaussian right

/-- The determinant factor `1 - denominatorRatio * errorRatio` of the normalized basis. -/
private def gapVector :
  Gaussian.Basic.Canonical := 1 - denominatorRatio *
  errorRatio

/-- The quadrance of the normalized stage-two determinant factor. -/
private def gap : Fraction.Rational :=
  Gaussian.Norm.Basic.normSq gapVector

/-- The displayed normalized determinant gap is positive. -/
private theorem gap_pos : 0 <
  gap := by decide

/-- The displayed error ratio has strict slack in the coefficient quadrance estimate. -/
private theorem error_margin :
    2 * (1 + Gaussian.Norm.Basic.normSq errorRatio) <
      4 * gap := by
  decide

/-- The displayed denominator ratio has strict slack in the coefficient quadrance estimate. -/
private theorem denominator_margin :
    2 * (1 + Gaussian.Norm.Basic.normSq denominatorRatio) <
      4 * gap := by
  decide

/-- Eliminating the trailing coefficient recovers the leading coefficient times the normalized determinant factor. -/
private theorem left_gap_identity
    (left right : GaussianInt) :
    GaussianInt.toGaussian left * gapVector =
      normalizedError left right -
        normalizedDenominator left right *
          errorRatio := by
  apply Gaussian.Basic.ext <;>
    simp only [gapVector, normalizedError,
      normalizedDenominator,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;>
    ring1

/-- Eliminating the leading coefficient recovers the trailing coefficient times the normalized determinant factor. -/
private theorem right_gap_identity
    (left right : GaussianInt) :
    GaussianInt.toGaussian right * gapVector =
      normalizedDenominator left right -
        denominatorRatio * normalizedError left
          right := by
  apply Gaussian.Basic.ext <;>
    simp only [gapVector, normalizedError,
      normalizedDenominator,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;>
    ring1

/-- Unit bounds on both normalized coordinates force both coefficient quadrances below four.

The two elimination identities and explicit positive margins provide finite bounds for the Gaussian integer
coefficients. -/
private theorem
  coefficient_normNat_lt_four
    (left right : GaussianInt)
    (errorBound :
      Gaussian.Norm.Basic.normSq
        (normalizedError left right) ≤ 1)
    (denominatorBound :
      Gaussian.Norm.Basic.normSq
        (normalizedDenominator left right) ≤ 1) :
    Data.GaussianInt.normNat left < 4 ∧ Data.GaussianInt.normNat right < 4 := by
  have errorNormNonnegative :
      (0 : Fraction.Rational) ≤
        Gaussian.Norm.Basic.normSq errorRatio :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have denominatorNormNonnegative :
      (0 : Fraction.Rational) ≤
        Gaussian.Norm.Basic.normSq denominatorRatio :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have denominatorScaledLe :
      Gaussian.Norm.Basic.normSq
            (normalizedDenominator left right) *
          Gaussian.Norm.Basic.normSq errorRatio ≤
        Gaussian.Norm.Basic.normSq errorRatio := by
    calc
      _ ≤ (1 : Fraction.Rational) *
          Gaussian.Norm.Basic.normSq Initial.errorRatio :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          denominatorBound errorNormNonnegative
      _ = _ := by ring1
  have errorScaledLe :
      Gaussian.Norm.Basic.normSq
            (normalizedError left right) *
          Gaussian.Norm.Basic.normSq denominatorRatio ≤
        Gaussian.Norm.Basic.normSq denominatorRatio := by
    calc
      _ ≤ (1 : Fraction.Rational) *
          Gaussian.Norm.Basic.normSq Initial.denominatorRatio :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          errorBound denominatorNormNonnegative
      _ = _ := by ring1
  have leftSumBound :
      Gaussian.Norm.Basic.normSq
            (normalizedError left right) +
          Gaussian.Norm.Basic.normSq
            (normalizedDenominator left right *
              errorRatio) ≤
        1 + Gaussian.Norm.Basic.normSq errorRatio := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Arithmetic.add_le_add_direct
      errorBound denominatorScaledLe
  have rightSumBound :
      Gaussian.Norm.Basic.normSq
            (normalizedDenominator left right) +
          Gaussian.Norm.Basic.normSq
            (denominatorRatio * normalizedError
              left right) ≤
        1 + Gaussian.Norm.Basic.normSq denominatorRatio := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    apply Arithmetic.add_le_add_direct denominatorBound
    calc
      Gaussian.Norm.Basic.normSq denominatorRatio *
          Gaussian.Norm.Basic.normSq
            (normalizedError left right) =
        Gaussian.Norm.Basic.normSq
            (normalizedError left right) *
          Gaussian.Norm.Basic.normSq Initial.denominatorRatio := by
        ring1
      _ ≤ Gaussian.Norm.Basic.normSq Initial.denominatorRatio :=
        errorScaledLe
  have leftProductStrict :
      (GaussianInt.normNat left : Fraction.Rational) * gap < 4 *
        gap := by
    calc
      (GaussianInt.normNat left : Fraction.Rational) * gap =
          Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian left * gapVector) := by
        unfold gap
        rw [Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian]
      _ = Gaussian.Norm.Basic.normSq
          (normalizedError left right -
            normalizedDenominator left right *
              errorRatio) := by
        rw [left_gap_identity]
      _ ≤ 2 *
          (Gaussian.Norm.Basic.normSq
              (normalizedError left right) +
            Gaussian.Norm.Basic.normSq
              (normalizedDenominator left right *
                errorRatio)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + Gaussian.Norm.Basic.normSq errorRatio) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          leftSumBound (by decide)
      _ < 4 * Initial.gap := error_margin
  have rightProductStrict :
      (GaussianInt.normNat right : Fraction.Rational) * gap < 4 *
        gap := by
    calc
      (GaussianInt.normNat right : Fraction.Rational) * gap =
          Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian right * gapVector) := by
        unfold gap
        rw [Gaussian.Norm.Basic.normSq_mul,
          GaussianInt.normSq_toGaussian]
      _ = Gaussian.Norm.Basic.normSq
          (normalizedDenominator left right -
            denominatorRatio * normalizedError
              left right) := by
        rw [right_gap_identity]
      _ ≤ 2 *
          (Gaussian.Norm.Basic.normSq
              (normalizedDenominator left right) +
            Gaussian.Norm.Basic.normSq
              (denominatorRatio *
                normalizedError left right)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 *
          (1 + Gaussian.Norm.Basic.normSq denominatorRatio) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          rightSumBound (by decide)
      _ < 4 * Initial.gap := denominator_margin
  constructor
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Arithmetic.lt_of_mul_lt_mul_right_direct
      leftProductStrict gap_pos
  · apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
    exact Arithmetic.lt_of_mul_lt_mul_right_direct
      rightProductStrict gap_pos

/-- Two nonzero coefficients of quadrance below four give a strict normalized cylinder exterior.

Unit and diagonal classification reduces the assertion to finitely many exact rational coordinate checks. -/
private theorem
  small_nonzero_strictly_exterior
    (left right : GaussianInt) (leftNonzero : left ≠ 0)
    (rightNonzero : right ≠ 0) (leftSmall : Data.GaussianInt.normNat left < 4)
    (rightSmall : Data.GaussianInt.normNat right < 4) :
    (1 : Fraction.Rational) <
        Gaussian.Norm.Basic.normSq
          (normalizedError left right) ∨
      1 < Gaussian.Norm.Basic.normSq
        (normalizedDenominator left right) := by
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
    (1 : Fraction.Rational) <
        Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian left + GaussianInt.toGaussian right *
            (⟨SignedFraction.Normalization.ofFraction ⟨1, 2, by decide⟩,
              SignedFraction.Normalization.ofFraction ⟨1, 8, by decide⟩⟩ :
              Gaussian.Basic.Canonical)) ∨
      1 < Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian left *
            (⟨SignedFraction.Normalization.ofFraction ⟨15, 112, by decide⟩,
              -SignedFraction.Normalization.ofFraction ⟨1, 2, by decide⟩⟩ :
              Gaussian.Basic.Canonical) + GaussianInt.toGaussian right) := by
  change (1 : Fraction.Rational) < Gaussian.Norm.Basic.normSq
      (normalizedError left right) ∨
    1 < Gaussian.Norm.Basic.normSq (normalizedDenominator left right)
  by_cases errorExterior :
      (1 : Fraction.Rational) <
        Gaussian.Norm.Basic.normSq
          (normalizedError left right)
  · exact Or.inl errorExterior
  · by_cases denominatorExterior :
        (1 : Fraction.Rational) <
          Gaussian.Norm.Basic.normSq
            (normalizedDenominator left right)
    · exact Or.inr denominatorExterior
    · have small := coefficient_normNat_lt_four left right
        (le_of_not_gt errorExterior) (le_of_not_gt denominatorExterior)
      exact small_nonzero_strictly_exterior left right leftNonzero
        rightNonzero small.1 small.2

/-- The finite Pell parameter at stage one is `4/15`. -/
private theorem pellParameter_one :
    Parameter.pellParameter 1 =
      fourOverFifteen := by
  decide

/-- The critical error ratio at stage one is `(1/2, 2/15)`. -/
private theorem criticalErrorRatio_one :
    Cylinder.Basic.criticalErrorRatio
        (Parameter.pellParameter 1) =
      ⟨oneHalf, twoOverFifteen⟩ := by
  rw [pellParameter_one]
  apply Gaussian.Basic.ext <;> decide

/-- The real Gaussian factor `4/15` scaling the lower error after the initial transition. -/
private def lowerErrorScale :
  Gaussian.Basic.Canonical := ⟨fourOverFifteen, 0⟩

/-- The lower transition coefficients produce the retained lower-error scale. -/
private theorem lowerCombinationFactor :
    GaussianInt.toGaussian Transition.lowerFromLower +
        GaussianInt.toGaussian Transition.lowerFromUpper *
          (⟨oneHalf, twoOverFifteen⟩ :
            Gaussian.Basic.Canonical) =
      lowerErrorScale := by
  apply Gaussian.Basic.ext <;> decide

/-- The upper transition coefficients produce the lower-error scale times the new error ratio. -/
private theorem upperCombinationFactor :
    GaussianInt.toGaussian Transition.upperFromLower +
        GaussianInt.toGaussian Transition.upperFromUpper *
          (⟨oneHalf, twoOverFifteen⟩ :
            Gaussian.Basic.Canonical) =
      lowerErrorScale * errorRatio := by
  apply Gaussian.Basic.ext <;> decide

/-- The lower stage-two error at the stage-one source is the old lower error times `4/15`. -/
private theorem stageTwo_error_lower :
    Best.Error.error
        (Pair.criticalSource 1).value
        (Pair.criticalLowerPair 2) =
      Pair.criticalLowerError 1 * lowerErrorScale := by
  rw [show (2 : Nat) = 1 + 1 by rfl,
    Transition.criticalLowerPair_succ,
    Best.Error.error_linearCombination,
    Pair.criticalSource_error_lower,
    Pair.criticalSource_error_upper,
    criticalErrorRatio_one]
  calc
    GaussianInt.toGaussian Transition.lowerFromLower *
          Pair.criticalLowerError 1 +
        GaussianInt.toGaussian Transition.lowerFromUpper *
          (Pair.criticalLowerError 1 *
            (⟨oneHalf, twoOverFifteen⟩ :
              Gaussian.Basic.Canonical)) =
      Pair.criticalLowerError 1 *
        (GaussianInt.toGaussian Transition.lowerFromLower +
          GaussianInt.toGaussian Transition.lowerFromUpper *
            (⟨oneHalf, twoOverFifteen⟩ :
              Gaussian.Basic.Canonical)) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = Pair.criticalLowerError 1 *
        Initial.lowerErrorScale := by rw
          [lowerCombinationFactor]

/-- The upper stage-two error at the stage-one source is the scaled lower error times the new error ratio. -/
private theorem stageTwo_error_upper :
    Best.Error.error
        (Pair.criticalSource 1).value
        (Pair.criticalUpperPair 2) =
      (Pair.criticalLowerError 1 * lowerErrorScale) *
        errorRatio := by
  rw [show (2 : Nat) = 1 + 1 by rfl,
    Transition.criticalUpperPair_succ,
    Best.Error.error_linearCombination,
    Pair.criticalSource_error_lower,
    Pair.criticalSource_error_upper,
    criticalErrorRatio_one]
  calc
    GaussianInt.toGaussian Transition.upperFromLower *
          Pair.criticalLowerError 1 +
        GaussianInt.toGaussian Transition.upperFromUpper *
          (Pair.criticalLowerError 1 *
            (⟨oneHalf, twoOverFifteen⟩ :
              Gaussian.Basic.Canonical)) =
      Pair.criticalLowerError 1 *
        (GaussianInt.toGaussian Transition.upperFromLower +
          GaussianInt.toGaussian Transition.upperFromUpper *
            (⟨oneHalf, twoOverFifteen⟩ :
              Gaussian.Basic.Canonical)) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = Pair.criticalLowerError 1 *
        (lowerErrorScale * errorRatio) := by rw
          [upperCombinationFactor]
    _ = (Pair.criticalLowerError 1 *
          lowerErrorScale) * Initial.errorRatio := by
      rw [Gaussian.Basic.mul_assoc]

/-- The lower stage-two denominator is the upper one multiplied by the retained normalized denominator ratio. -/
private theorem stageTwo_denominator_lower
  :
    GaussianInt.toGaussian
        (Pair.criticalLowerPair 2).denominator =
      GaussianInt.toGaussian
          (Pair.criticalUpperPair 2).denominator *
        denominatorRatio := open Purelib.NumberTheory in by
  have parameterTwo :
      Parameter.pellParameter 2 =
        fifteenOverFiftySix := by
    have fiftySixPositive : (0 : Fraction.Rational) < (56 : Fraction.Rational) :=
      Fraction.Cast.Order.natCast_pos_direct (by decide)
    apply Fraction.Field.mul_right_cancel_of_ne
      (c := (56 : Fraction.Rational)) fiftySixPositive.ne'
    calc
      Parameter.pellParameter 2 * (56 : Fraction.Rational) =
          (15 : Fraction.Rational) := by
        rewrite [Parameter.pellParameter_eq_castRatio]
        rw [show Pell.FiniteBranch.pellNumerator 2 = 15 by decide,
          show Pell.FiniteBranch.pellDenominator 2 = 56 by decide]
        exact Fraction.Field.div_mul_cancel_of_ne _ _
          fiftySixPositive.ne'
      _ = fifteenOverFiftySix * (56 : Fraction.Rational) :=
        fifteenOverFiftySix_mul_denominator.symm
  have ratioTwo :
      Cylinder.Basic.criticalDenominatorRatio
          (Parameter.pellParameter 2) =
        denominatorRatio := by
    rw [parameterTwo]
    apply Gaussian.Basic.ext <;> decide
  have upperNonzero :
      GaussianInt.toGaussian
          (Pair.criticalUpperPair 2).denominator ≠ 0 := by
    intro zero
    exact Pair.criticalUpper_denominator_ne_zero 2
      (GaussianInt.toGaussian_eq_zero.mp zero)
  have ratioIdentity :=
    Pair.criticalPair_denominatorRatio 2
  rw [ratioTwo] at ratioIdentity
  calc
    GaussianInt.toGaussian
          (Pair.criticalLowerPair 2).denominator =
        Window.Basic.denominatorRatio
            (Pair.criticalLowerPair 2)
            (Pair.criticalUpperPair 2) *
          GaussianInt.toGaussian
            (Pair.criticalUpperPair 2).denominator := by
      unfold Window.Basic.denominatorRatio
      rw [Gaussian.Basic.mul_assoc,
        Gaussian.Field.inv_mul _ upperNonzero,
        Gaussian.Basic.mul_one]
    _ = denominatorRatio *
          GaussianInt.toGaussian
            (Pair.criticalUpperPair 2).denominator := by
      rw [ratioIdentity]
    _ = GaussianInt.toGaussian
          (Pair.criticalUpperPair 2).denominator *
        Initial.denominatorRatio := by
      rw [Gaussian.Basic.mul_comm]

/-- A stage-two coefficient combination factors its error into the retained scale and normalized error coordinate. -/
private theorem
  stageTwo_error_linearCombination
    (left right : GaussianInt) :
    Best.Error.error
        (Pair.criticalSource 1).value
        (Data.GaussianInt.Pair.LinearCombination.linearCombination
          (Pair.criticalLowerPair 2)
          (Pair.criticalUpperPair 2) left right) =
      (Pair.criticalLowerError 1 * lowerErrorScale) *
        normalizedError left right := by
  rw [Best.Error.error_linearCombination, stageTwo_error_lower,
    stageTwo_error_upper]
  unfold normalizedError
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- A stage-two coefficient combination factors its denominator into the upper denominator and normalized coordinate. -/
private theorem
  stageTwo_denominator_linearCombination
    (left right : GaussianInt) :
    GaussianInt.toGaussian
        (Data.GaussianInt.Pair.LinearCombination.linearCombination
          (Pair.criticalLowerPair 2)
          (Pair.criticalUpperPair 2)
          left right).denominator =
      GaussianInt.toGaussian
          (Pair.criticalUpperPair 2).denominator *
        normalizedDenominator left right := by
  simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
    GaussianInt.toGaussian_mul]
  rw [stageTwo_denominator_lower]
  unfold normalizedDenominator
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- The scaled lower stage-two error at the stage-one source has positive quadrance. -/
private theorem
  stageTwo_lowerError_normSq_pos :
    0 < Gaussian.Norm.Basic.normSq
      (Pair.criticalLowerError 1 *
        lowerErrorScale) := by
  have firstWindow :=
    Pair.criticalPairs_areConsecutiveBest 1
  have nativeErrorOrder :
      Best.Error.errorQuadrance
          (Pair.criticalSource 1).value
          (Pair.criticalUpperPair 1) <
        Best.Error.errorQuadrance
          (Pair.criticalSource 1).value
          (Pair.criticalLowerPair 1) :=
    firstWindow.2.1.2.1 _ firstWindow.1.1 firstWindow.2.2.1
  have oldLowerPositive :
      0 < Gaussian.Norm.Basic.normSq
        (Pair.criticalLowerError 1) := by
    rw [← Pair.criticalSource_error_lower]
    exact (Gaussian.Norm.Basic.normSq_nonneg _).trans_lt
      nativeErrorOrder
  have scalePositive :
      0 < Gaussian.Norm.Basic.normSq lowerErrorScale := by
    decide
  rw [Gaussian.Norm.Basic.normSq_mul]
  exact Arithmetic.mul_pos_direct oldLowerPositive scalePositive

/-- The embedded upper stage-two denominator has positive quadrance. -/
private theorem
  stageTwo_upperDenominator_normSq_pos :
    0 < Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian
        (Pair.criticalUpperPair 2).denominator) := by
  apply Gaussian.Norm.Basic.normSq_pos
  intro zero
  exact Pair.criticalUpper_denominator_ne_zero 2
    (GaussianInt.toGaussian_eq_zero.mp zero)

/-- The exact strict-basis certificate for the second window at the fixed
stage-one rational source. -/
theorem stageTwoStrictExteriorCertificate
  :
    Best.Cylinder.Basis.StrictExteriorCertificate
      (Pair.criticalSource 1).value
      (Pair.criticalLowerPair 2)
      (Pair.criticalUpperPair 2) := by
  refine
    { indexOne := Pair.criticalPair_indexOne 2
      lowerDenominatorNonzero :=
        Pair.criticalLower_denominator_ne_zero 2
      upperDenominatorNonzero :=
        Pair.criticalUpper_denominator_ne_zero 2
      errorOrder := ?_
      denominatorOrder :=
        Pair.critical_denominatorQuadrance_ordered 2
      bothNonzeroExterior := ?_ }
  · unfold Best.Error.errorQuadrance
    rw [stageTwo_error_lower,
      stageTwo_error_upper]
    have ratioStrict :
        Gaussian.Norm.Basic.normSq errorRatio < 1 := by
      decide
    calc
      Gaussian.Norm.Basic.normSq
          ((Pair.criticalLowerError 1 *
            lowerErrorScale) * errorRatio) =
        Gaussian.Norm.Basic.normSq
            (Pair.criticalLowerError 1 *
              lowerErrorScale) *
          Gaussian.Norm.Basic.normSq Initial.errorRatio := by
        rw [Gaussian.Norm.Basic.normSq_mul]
      _ < Gaussian.Norm.Basic.normSq
            (Pair.criticalLowerError 1 *
              lowerErrorScale) * 1 :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          stageTwo_lowerError_normSq_pos ratioStrict
      _ = Gaussian.Norm.Basic.normSq
          (Pair.criticalLowerError 1 *
            lowerErrorScale) := by ring1
  · intro left right leftNonzero rightNonzero
    rcases normalized_strictExterior left right leftNonzero rightNonzero with
      errorExterior | denominatorExterior
    · left
      unfold Best.Error.errorQuadrance
      rw [stageTwo_error_lower,
        stageTwo_error_linearCombination]
      calc
        Gaussian.Norm.Basic.normSq
            (Pair.criticalLowerError 1 *
              lowerErrorScale) =
          Gaussian.Norm.Basic.normSq
              (Pair.criticalLowerError 1 *
                lowerErrorScale) * 1 := by ring1
        _ < Gaussian.Norm.Basic.normSq
              (Pair.criticalLowerError 1 *
                lowerErrorScale) *
            Gaussian.Norm.Basic.normSq
              (normalizedError left right) :=
          Arithmetic.mul_lt_mul_of_pos_left_direct
            stageTwo_lowerError_normSq_pos errorExterior
        _ = Gaussian.Norm.Basic.normSq
            ((Pair.criticalLowerError 1 *
              lowerErrorScale) * normalizedError
                left right) := by
          exact
            (Gaussian.Norm.Basic.normSq_mul
              (Pair.criticalLowerError 1 *
                lowerErrorScale)
                  (normalizedError left right)).symm
    · right
      apply (Fraction.Cast.Order.natCast_lt_iff_direct).1
      unfold Best.Error.denominatorQuadrance
      rw [← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
        stageTwo_denominator_linearCombination]
      calc
        Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
              (Pair.criticalUpperPair 2).denominator) =
          Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Pair.criticalUpperPair 2).denominator) *
            1 := by ring1
        _ < Gaussian.Norm.Basic.normSq
              (GaussianInt.toGaussian
                (Pair.criticalUpperPair 2).denominator) *
            Gaussian.Norm.Basic.normSq
              (normalizedDenominator left right) :=
          Arithmetic.mul_lt_mul_of_pos_left_direct
            stageTwo_upperDenominator_normSq_pos denominatorExterior
        _ = Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
                (Pair.criticalUpperPair 2).denominator *
              normalizedDenominator left right) := by
          rw [Gaussian.Norm.Basic.normSq_mul]

/-- The next Pell pair basis is a genuine consecutive-best window for the
same rational source as the preceding stage-one window. -/
theorem
  stageTwo_areConsecutiveBest_at_stageOneSource
  :
    Best.Consecutive.Basic.AreConsecutiveBest
      (Pair.criticalSource 1).value
      (Pair.criticalLowerPair 2)
      (Pair.criticalUpperPair 2) :=
  Initial.stageTwoStrictExteriorCertificate.areConsecutiveBest

/-- Constructive two-window feasibility: one displayed rational source
supports two strictly scale-separated critical Pell windows. -/
theorem
  criticalSource_one_supports_two_windows
  :
    Best.Consecutive.Basic.AreConsecutiveBest
        (Pair.criticalSource 1).value
        (Pair.criticalLowerPair 1)
        (Pair.criticalUpperPair 1) ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (Pair.criticalSource 1).value
        (Pair.criticalLowerPair 2)
        (Pair.criticalUpperPair 2) ∧
      Best.Error.denominatorQuadrance
          (Pair.criticalUpperPair 1) <
        Best.Error.denominatorQuadrance
          (Pair.criticalLowerPair 2) :=
  ⟨Pair.criticalPairs_areConsecutiveBest 1,
    stageTwo_areConsecutiveBest_at_stageOneSource,
    Transition.criticalUpper_lt_nextLower_denominatorQuadrance 1⟩

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Initial

end
