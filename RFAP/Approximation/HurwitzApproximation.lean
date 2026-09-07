import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzRational

/-!
# Finite approximation algebra for Hurwitz convergents

This module isolates the calculation underlying a second-kind approximation
comparison.  The error of `p/q` is represented without division as `qz-p`.
Adjacent finite continuants have determinant `1` or `-1`, so every displayed
Gaussian-integer competitor has explicit coefficients in that adjacent
continuant basis.  No enumeration of Gaussian rationals is used.
-/

namespace RFAP.HurwitzApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev ConvergentPair := RFAP.HurwitzRational.ConvergentPair
abbrev Fraction := RFAP.HurwitzRational.Fraction

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.HurwitzRational

/-- Division-free error of the displayed pair `p/q` at `source`: `qz-p`. -/
def error (source : Gaussian) (pair : ConvergentPair) : Gaussian :=
  source * toGaussian pair.denominator - toGaussian pair.numerator

/-- A competitor-wise second-kind comparison.  Keeping the competitor as an
explicit argument makes each use a finite, checkable statement. -/
def AtLeastAsGoodAs (source : Gaussian)
    (convergent competitor : ConvergentPair) : Prop :=
  normSq (error source convergent) ≤ normSq (error source competitor)

/-- Cross determinant of two integral numerator/denominator pairs. -/
def determinant (left right : ConvergentPair) : GaussianInt :=
  left.numerator * right.denominator -
    right.numerator * left.denominator

/-- The explicit finite alternative to saying that a determinant is a unit. -/
def HasUnitDeterminant (left right : ConvergentPair) : Prop :=
  determinant left right = 1 ∨ determinant left right = -1

theorem determinant_prepend (digit : GaussianInt)
    (left right : ConvergentPair) :
    determinant (prepend digit left) (prepend digit right) =
      -determinant left right := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [determinant, prepend,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- Every pair of adjacent finite continuants has determinant `1` or `-1`.
The proof follows the displayed digit list and merely flips the sign at each
front digit. -/
theorem adjacent_hasUnitDeterminant (initialDigits : List GaussianInt)
    (nextDigit : GaussianInt) :
    HasUnitDeterminant
      (continuant (initialDigits ++ [nextDigit]))
      (continuant initialDigits) := by
  induction initialDigits with
  | nil =>
      right
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [List.nil_append, determinant, continuant, prepend,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im] <;>
        ring1
  | cons head tail inductionHypothesis =>
      rw [List.cons_append, continuant_cons, continuant_cons,
        HasUnitDeterminant, determinant_prepend]
      rcases inductionHypothesis with positive | negative
      · right
        rw [positive]
      · left
        rw [negative]
        exact neg_neg 1

theorem determinant_mul_self_eq_one {left right : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant left right) :
    determinant left right * determinant left right = 1 := by
  rcases unitDeterminant with positive | negative
  · rw [positive]
    exact RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul 1
  · rw [negative]
    ring1

/-- Coefficient of `current` in the explicit adjacent-continuant expansion
of `competitor`. -/
def currentCoefficient (current previous competitor : ConvergentPair) :
    GaussianInt :=
  determinant current previous * determinant competitor previous

/-- Coefficient of `previous` in the explicit adjacent-continuant expansion
of `competitor`. -/
def previousCoefficient (current previous competitor : ConvergentPair) :
    GaussianInt :=
  determinant current previous * determinant current competitor

/-- Numerator half of the adjacent-continuant basis calculation. -/
theorem competitor_numerator_decomposition
    {current previous competitor : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant current previous) :
    currentCoefficient current previous competitor * current.numerator +
        previousCoefficient current previous competitor * previous.numerator =
      competitor.numerator := by
  have square := determinant_mul_self_eq_one unitDeterminant
  have algebraic :
      currentCoefficient current previous competitor * current.numerator +
          previousCoefficient current previous competitor *
            previous.numerator =
        (determinant current previous * determinant current previous) *
          competitor.numerator := by
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
      simp only [currentCoefficient, previousCoefficient, determinant,
        RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
      ring1
  rw [algebraic, square]
  exact RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul _

/-- Denominator half of the adjacent-continuant basis calculation. -/
theorem competitor_denominator_decomposition
    {current previous competitor : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant current previous) :
    currentCoefficient current previous competitor * current.denominator +
        previousCoefficient current previous competitor * previous.denominator =
      competitor.denominator := by
  have square := determinant_mul_self_eq_one unitDeterminant
  have algebraic :
      currentCoefficient current previous competitor * current.denominator +
          previousCoefficient current previous competitor *
            previous.denominator =
        (determinant current previous * determinant current previous) *
          competitor.denominator := by
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
      simp only [currentCoefficient, previousCoefficient, determinant,
        RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
      ring1
  rw [algebraic, square]
  exact RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul _

/-- The competitor error is the same explicit integral combination of the
two adjacent convergent errors.  This is the algebraic reduction used by the
Lakein comparison; the remaining work is the finite Hurwitz-square geometry
that bounds this combination. -/
theorem competitor_error_decomposition
    (source : Gaussian) {current previous competitor : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant current previous) :
    error source competitor =
      toGaussian (currentCoefficient current previous competitor) *
          error source current +
        toGaussian (previousCoefficient current previous competitor) *
          error source previous := by
  have numerator := competitor_numerator_decomposition
    (competitor := competitor) unitDeterminant
  have denominator := competitor_denominator_decomposition
    (competitor := competitor) unitDeterminant
  unfold error
  rw [← numerator, ← denominator]
  simp only [toGaussian_add, toGaussian_mul]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

/-- Pair representing an integral Gaussian-rational competitor. -/
def integralPair (value : GaussianInt) : ConvergentPair := ⟨value, 1⟩

theorem firstConvergent_error (fraction : Fraction) :
    error fraction.value (continuant [RFAP.HurwitzRational.digit fraction]) =
      RFAP.HurwitzRational.residual fraction := by
  simp only [error, continuant, prepend,
    RFAP.ConstructiveGaussianHeight.GaussianInt.mul_one,
    RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero, toGaussian_one,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    RFAP.HurwitzRational.residual, RFAP.HurwitzRational.digit,
    RFAP.HurwitzNearest.remainder]

/-- The first Hurwitz convergent is already second-kind optimal against every
displayed Gaussian integer. -/
theorem firstConvergent_atLeastAsGoodAs_integral
    (fraction : Fraction) (competitor : GaussianInt) :
    AtLeastAsGoodAs fraction.value
      (continuant [RFAP.HurwitzRational.digit fraction])
      (integralPair competitor) := by
  rw [AtLeastAsGoodAs, firstConvergent_error]
  simpa only [RFAP.HurwitzRational.residual, error, integralPair,
    toGaussian_one, RFAP.ConstructiveGaussian.Gaussian.mul_one]
    using RFAP.HurwitzNearest.remainder_normSq_le_competitor
      fraction.value competitor

/-- The complete finite encoding reconstructs its displayed source, hence
has zero division-free error. -/
theorem encodedConvergent_error_eq_zero (fraction : Fraction) :
    error fraction.value (continuant (encode fraction)) = 0 := by
  rw [error, encode_reconstruct fraction]
  exact RFAP.ConstructiveGaussian.Gaussian.sub_self _

/-- The final convergent is exact and therefore compares weakly with every
displayed competitor.  The nontrivial Lakein theorem concerns all earlier
convergents; its algebraic reduction is `competitor_error_decomposition`. -/
theorem encodedConvergent_atLeastAsGoodAs (fraction : Fraction)
    (competitor : ConvergentPair) :
    AtLeastAsGoodAs fraction.value (continuant (encode fraction)) competitor := by
  rw [AtLeastAsGoodAs, encodedConvergent_error_eq_zero, normSq_zero]
  exact normSq_nonneg _

end RFAP.HurwitzApproximation
