import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzApproximation

/-!
# Finite traces of Hurwitz complete quotients

The terminating rational encoder is useful for execution, while the Lakein
comparison also needs the complete quotient and the two adjacent convergents
at every prefix.  This module records exactly that finite state.  Each stage
carries a division-free reconstruction identity for the original displayed
Gaussian rational.
-/

namespace RFAP.HurwitzTrace

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev ConvergentPair := RFAP.HurwitzRational.ConvergentPair

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.HurwitzRational
open RFAP.HurwitzApproximation

/-- Chronological continuant recurrence
`(p,q) ↦ a(p,q) + (p₋,q₋)`. -/
def advancePair (nextDigit : GaussianInt)
    (current previous : ConvergentPair) : ConvergentPair :=
  ⟨nextDigit * current.numerator + previous.numerator,
    nextDigit * current.denominator + previous.denominator⟩

theorem determinant_advancePair (nextDigit : GaussianInt)
    (current previous : ConvergentPair) :
    determinant (advancePair nextDigit current previous) current =
      -determinant current previous := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [determinant, advancePair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

theorem unitDeterminant_advancePair {current previous : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant current previous)
    (nextDigit : GaussianInt) :
    HasUnitDeterminant (advancePair nextDigit current previous) current := by
  rw [HasUnitDeterminant, determinant_advancePair]
  rcases unitDeterminant with positive | negative
  · right
    rw [positive]
  · left
    rw [negative]
    exact neg_neg 1

/-- One generated prefix, retaining its complete quotient and its two
adjacent integral continuants. -/
structure Stage (source : Fraction) where
  quotient : Fraction
  previous : ConvergentPair
  current : ConvergentPair
  unitDeterminant : HasUnitDeterminant current previous
  represents :
    source.value *
        (toGaussian current.denominator +
          residual quotient * toGaussian previous.denominator) =
      toGaussian current.numerator +
        residual quotient * toGaussian previous.numerator

theorem Stage.error_add_residual_mul_previous_eq_zero
    {source : Fraction} (stage : Stage source) :
    error source.value stage.current +
        residual stage.quotient * error source.value stage.previous = 0 := by
  calc
    error source.value stage.current +
          residual stage.quotient * error source.value stage.previous =
        source.value *
            (toGaussian stage.current.denominator +
              residual stage.quotient *
                toGaussian stage.previous.denominator) -
          (toGaussian stage.current.numerator +
            residual stage.quotient *
              toGaussian stage.previous.numerator) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [error,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = 0 := by
      rw [stage.represents]
      exact RFAP.ConstructiveGaussian.Gaussian.sub_self _

theorem Stage.previous_error_eq_neg_next_mul_current
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) :
    error source.value stage.previous =
      -(next stage.quotient nonterminal).value *
        error source.value stage.current := by
  have residualNonzero : residual stage.quotient ≠ 0 :=
    residual_ne_zero nonterminal
  have reciprocal :
      (next stage.quotient nonterminal).value *
          residual stage.quotient = 1 := by
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ residualNonzero]
  have residualMulPrevious :
      residual stage.quotient * error source.value stage.previous =
        -error source.value stage.current := by
    calc
      residual stage.quotient * error source.value stage.previous =
          (error source.value stage.current +
            residual stage.quotient * error source.value stage.previous) -
              error source.value stage.current := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
          ring1
      _ = 0 - error source.value stage.current := by
        rw [stage.error_add_residual_mul_previous_eq_zero]
      _ = -error source.value stage.current := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.neg_re,
            RFAP.ConstructiveGaussian.Gaussian.neg_im,
            RFAP.ConstructiveGaussian.Gaussian.zero_re,
            RFAP.ConstructiveGaussian.Gaussian.zero_im] <;>
          ring1
  calc
    error source.value stage.previous =
        ((next stage.quotient nonterminal).value *
          residual stage.quotient) * error source.value stage.previous := by
      rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]
    _ = (next stage.quotient nonterminal).value *
          (residual stage.quotient *
            error source.value stage.previous) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = (next stage.quotient nonterminal).value *
          (-error source.value stage.current) := by
      rw [residualMulPrevious]
    _ = -(next stage.quotient nonterminal).value *
          error source.value stage.current := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1

/-- At a nonterminal prefix, a competitor error is the current error times
the explicit Lakein factor `s-t xₙ₊₁`. -/
theorem Stage.competitor_error_eq_factor_mul_current
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0)
    (competitor : ConvergentPair) :
    error source.value competitor =
      (toGaussian
          (currentCoefficient stage.current stage.previous competitor) -
        toGaussian
          (previousCoefficient stage.current stage.previous competitor) *
            (next stage.quotient nonterminal).value) *
        error source.value stage.current := by
  rw [competitor_error_decomposition source.value stage.unitDeterminant,
    stage.previous_error_eq_neg_next_mul_current nonterminal]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

/-- The Lakein comparison is reduced to the quadrance-one exterior test for
the explicit factor. -/
theorem Stage.atLeastAsGoodAs_of_one_le_factor_normSq
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0)
    (competitor : ConvergentPair)
    (factorExterior :
      1 ≤ normSq
        (toGaussian
            (currentCoefficient stage.current stage.previous competitor) -
          toGaussian
              (previousCoefficient stage.current stage.previous competitor) *
            (next stage.quotient nonterminal).value)) :
    AtLeastAsGoodAs source.value stage.current competitor := by
  rw [AtLeastAsGoodAs,
    stage.competitor_error_eq_factor_mul_current nonterminal competitor,
    normSq_mul]
  have currentErrorNonnegative := normSq_nonneg (error source.value stage.current)
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      factorExterior currentErrorNonnegative
  calc
    normSq (error source.value stage.current) =
        1 * normSq (error source.value stage.current) := by ring1
    _ ≤ normSq
          (toGaussian
              (currentCoefficient stage.current stage.previous competitor) -
            toGaussian
                (previousCoefficient stage.current stage.previous competitor) *
              (next stage.quotient nonterminal).value) *
          normSq (error source.value stage.current) := scaled

/-- The unnormalised complete denominator
`xₙ₊₁ qₙ + qₙ₋₁`. -/
def Stage.completeDenominator {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) : Gaussian :=
  (next stage.quotient nonterminal).value *
      toGaussian stage.current.denominator +
    toGaussian stage.previous.denominator

theorem Stage.scaled_represents {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) :
    source.value * stage.completeDenominator nonterminal =
      (next stage.quotient nonterminal).value *
          toGaussian stage.current.numerator +
        toGaussian stage.previous.numerator := by
  have residualNonzero : residual stage.quotient ≠ 0 :=
    residual_ne_zero nonterminal
  have reciprocal :
      (next stage.quotient nonterminal).value *
          residual stage.quotient = 1 := by
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ residualNonzero]
  calc
    source.value * stage.completeDenominator nonterminal =
        (next stage.quotient nonterminal).value *
          (source.value *
            (toGaussian stage.current.denominator +
              residual stage.quotient *
                toGaussian stage.previous.denominator)) := by
      unfold completeDenominator
      calc
        source.value *
              ((next stage.quotient nonterminal).value *
                  toGaussian stage.current.denominator +
                toGaussian stage.previous.denominator) =
            source.value *
              ((next stage.quotient nonterminal).value *
                  toGaussian stage.current.denominator +
                ((next stage.quotient nonterminal).value *
                    residual stage.quotient) *
                  toGaussian stage.previous.denominator) := by
          rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = (next stage.quotient nonterminal).value *
              (source.value *
                (toGaussian stage.current.denominator +
                  residual stage.quotient *
                    toGaussian stage.previous.denominator)) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
    _ = (next stage.quotient nonterminal).value *
          (toGaussian stage.current.numerator +
            residual stage.quotient *
              toGaussian stage.previous.numerator) := by
      rw [stage.represents]
    _ = (next stage.quotient nonterminal).value *
          toGaussian stage.current.numerator +
        toGaussian stage.previous.numerator := by
      calc
        (next stage.quotient nonterminal).value *
              (toGaussian stage.current.numerator +
                residual stage.quotient *
                  toGaussian stage.previous.numerator) =
            (next stage.quotient nonterminal).value *
                toGaussian stage.current.numerator +
              ((next stage.quotient nonterminal).value *
                  residual stage.quotient) *
                toGaussian stage.previous.numerator := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
        _ = (next stage.quotient nonterminal).value *
              toGaussian stage.current.numerator +
            toGaussian stage.previous.numerator := by
          rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]

/-- Determinant identity behind the exact convergent error formula. -/
theorem Stage.current_error_mul_completeDenominator
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) :
    error source.value stage.current *
        stage.completeDenominator nonterminal =
      -toGaussian (determinant stage.current stage.previous) := by
  have reconstruction := stage.scaled_represents nonterminal
  calc
    error source.value stage.current *
          stage.completeDenominator nonterminal =
        toGaussian stage.current.denominator *
            (source.value * stage.completeDenominator nonterminal) -
          toGaussian stage.current.numerator *
            stage.completeDenominator nonterminal := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [error,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = toGaussian stage.current.denominator *
          ((next stage.quotient nonterminal).value *
              toGaussian stage.current.numerator +
            toGaussian stage.previous.numerator) -
        toGaussian stage.current.numerator *
          stage.completeDenominator nonterminal := by
      rw [reconstruction]
    _ = -toGaussian (determinant stage.current stage.previous) := by
      unfold completeDenominator determinant
      simp only [toGaussian_sub, toGaussian_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1

theorem Stage.current_error_norm_product_eq_one
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) :
    normSq (error source.value stage.current) *
        normSq (stage.completeDenominator nonterminal) = 1 := by
  rw [← normSq_mul, stage.current_error_mul_completeDenominator nonterminal,
    normSq_neg, normSq_toGaussian]
  rcases stage.unitDeterminant with positive | negative
  · rw [positive]
    rfl
  · rw [negative]
    rfl

theorem Stage.current_error_normSq_pos
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) :
    0 < normSq (error source.value stage.current) := by
  have nonnegative := normSq_nonneg (error source.value stage.current)
  apply lt_of_le_of_ne nonnegative
  intro zero
  have product := stage.current_error_norm_product_eq_one nonterminal
  rw [← zero] at product
  have impossible : (0 : RFAP.ConstructiveFraction.Rational) = 1 := by
    calc
      0 = 0 * normSq (stage.completeDenominator nonterminal) := by ring1
      _ = 1 := product
  exact (show (0 : RFAP.ConstructiveFraction.Rational) ≠ 1 by decide) impossible

theorem Stage.completeDenominator_normSq_pos
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) :
    0 < normSq (stage.completeDenominator nonterminal) := by
  have nonnegative := normSq_nonneg (stage.completeDenominator nonterminal)
  apply lt_of_le_of_ne nonnegative
  intro zero
  have product := stage.current_error_norm_product_eq_one nonterminal
  rw [← zero] at product
  have impossible : (0 : RFAP.ConstructiveFraction.Rational) = 1 := by
    calc
      0 = normSq (error source.value stage.current) * 0 := by ring1
      _ = 1 := product
  exact (show (0 : RFAP.ConstructiveFraction.Rational) ≠ 1 by decide) impossible

/-- Cross determinant written as a difference of two scaled errors. -/
theorem determinant_eq_denominator_mul_error_sub
    (source : Gaussian) (current competitor : ConvergentPair) :
    toGaussian (determinant current competitor) =
      toGaussian current.denominator * error source competitor -
        toGaussian competitor.denominator * error source current := by
  unfold determinant error
  simp only [toGaussian_sub, toGaussian_mul]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

theorem determinant_normSq_le
    (source : Gaussian) (current competitor : ConvergentPair) :
    normSq (toGaussian (determinant current competitor)) ≤
      2 *
        ((normNat current.denominator :
            RFAP.ConstructiveFraction.Rational) *
            normSq (error source competitor) +
          (normNat competitor.denominator :
            RFAP.ConstructiveFraction.Rational) *
            normSq (error source current)) := by
  rw [determinant_eq_denominator_mul_error_sub]
  calc
    normSq
          (toGaussian current.denominator * error source competitor -
            toGaussian competitor.denominator * error source current) ≤
        2 *
          (normSq (toGaussian current.denominator * error source competitor) +
            normSq
              (toGaussian competitor.denominator * error source current)) :=
      normSq_sub_le_two _ _
    _ = 2 *
        ((normNat current.denominator :
            RFAP.ConstructiveFraction.Rational) *
            normSq (error source competitor) +
          (normNat competitor.denominator :
            RFAP.ConstructiveFraction.Rational) *
            normSq (error source current)) := by
      rw [normSq_mul, normSq_mul, normSq_toGaussian, normSq_toGaussian]

theorem Stage.previousCoefficient_normSq
    {source : Fraction} (stage : Stage source)
    (competitor : ConvergentPair) :
    (normNat
        (previousCoefficient stage.current stage.previous competitor) :
          RFAP.ConstructiveFraction.Rational) =
      normSq (toGaussian (determinant stage.current competitor)) := by
  rw [← normSq_toGaussian]
  unfold previousCoefficient
  rw [toGaussian_mul, normSq_mul]
  have determinantNorm :
      normSq (toGaussian (determinant stage.current stage.previous)) = 1 := by
    rcases stage.unitDeterminant with positive | negative
    · rw [positive, toGaussian_one, normSq_one]
    · rw [negative, toGaussian_neg, toGaussian_one, normSq_neg, normSq_one]
  rw [determinantNorm]
  ring1

/-- Lakein's large-`t` branch, in square-root-free form.  If the previous-basis
coefficient times the complete-denominator quadrance exceeds four current
denominator quadrances, no strictly smaller-denominator competitor can have a
smaller error. -/
theorem Stage.atLeastAsGoodAs_of_large_previousCoefficient
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0)
    (competitor : ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      normNat competitor.denominator < normNat stage.current.denominator)
    (largeCoefficient :
      (4 : RFAP.ConstructiveFraction.Rational) *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) <
        (normNat
            (previousCoefficient stage.current stage.previous competitor) :
              RFAP.ConstructiveFraction.Rational) *
          normSq (stage.completeDenominator nonterminal)) :
    AtLeastAsGoodAs source.value stage.current competitor := by
  rw [AtLeastAsGoodAs]
  apply le_of_not_gt
  intro competitorBetter
  have competitorHeightPositive :
      (0 : RFAP.ConstructiveFraction.Rational) <
        (normNat competitor.denominator :
          RFAP.ConstructiveFraction.Rational) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos competitorDenominatorNonzero)
  have denominatorCastSmaller :
      (normNat competitor.denominator :
          RFAP.ConstructiveFraction.Rational) <
        (normNat stage.current.denominator :
          RFAP.ConstructiveFraction.Rational) :=
    (RFAP.ConstructiveFraction.natCast_lt_iff_direct).2 denominatorSmaller
  have currentHeightPositive :
      (0 : RFAP.ConstructiveFraction.Rational) <
        (normNat stage.current.denominator :
          RFAP.ConstructiveFraction.Rational) :=
    competitorHeightPositive.trans denominatorCastSmaller
  have currentErrorPositive := stage.current_error_normSq_pos nonterminal
  have completeDenominatorPositive :=
    stage.completeDenominator_normSq_pos nonterminal
  have firstLeg :
      (normNat stage.current.denominator :
          RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value competitor) <
        (normNat stage.current.denominator :
          RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value stage.current) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      currentHeightPositive competitorBetter
  have secondLeg :
      (normNat competitor.denominator :
          RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value stage.current) <
        (normNat stage.current.denominator :
          RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value stage.current) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      denominatorCastSmaller currentErrorPositive
  have sumStrict := RFAP.ConstructiveFraction.add_lt_add_direct
    firstLeg secondLeg
  have doubledStrict :
      2 *
          ((normNat stage.current.denominator :
              RFAP.ConstructiveFraction.Rational) *
              normSq (error source.value competitor) +
            (normNat competitor.denominator :
              RFAP.ConstructiveFraction.Rational) *
              normSq (error source.value stage.current)) <
        4 *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value stage.current) := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (show (0 : RFAP.ConstructiveFraction.Rational) < 2 by decide)
        sumStrict
    calc
      2 *
            ((normNat stage.current.denominator :
                RFAP.ConstructiveFraction.Rational) *
                normSq (error source.value competitor) +
              (normNat competitor.denominator :
                RFAP.ConstructiveFraction.Rational) *
                normSq (error source.value stage.current)) <
          2 *
            ((normNat stage.current.denominator :
                RFAP.ConstructiveFraction.Rational) *
                normSq (error source.value stage.current) +
              (normNat stage.current.denominator :
                RFAP.ConstructiveFraction.Rational) *
                normSq (error source.value stage.current)) := scaled
      _ = 4 *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value stage.current) := by ring1
  have determinantStrict :
      normSq (toGaussian (determinant stage.current competitor)) <
        4 *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) *
          normSq (error source.value stage.current) :=
    (determinant_normSq_le source.value stage.current competitor).trans_lt
      doubledStrict
  have scaledDeterminantStrict :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      determinantStrict completeDenominatorPositive
  have coefficientProductStrict :
      (normNat
          (previousCoefficient stage.current stage.previous competitor) :
            RFAP.ConstructiveFraction.Rational) *
          normSq (stage.completeDenominator nonterminal) <
        4 *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) := by
    calc
      (normNat
            (previousCoefficient stage.current stage.previous competitor) :
              RFAP.ConstructiveFraction.Rational) *
            normSq (stage.completeDenominator nonterminal) =
          normSq (toGaussian (determinant stage.current competitor)) *
            normSq (stage.completeDenominator nonterminal) := by
        rw [stage.previousCoefficient_normSq competitor]
      _ < (4 *
            (normNat stage.current.denominator :
              RFAP.ConstructiveFraction.Rational) *
            normSq (error source.value stage.current)) *
          normSq (stage.completeDenominator nonterminal) :=
        scaledDeterminantStrict
      _ = 4 *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) *
          (normSq (error source.value stage.current) *
            normSq (stage.completeDenominator nonterminal)) := by ring1
      _ = 4 *
          (normNat stage.current.denominator :
            RFAP.ConstructiveFraction.Rational) := by
        rw [stage.current_error_norm_product_eq_one nonterminal]
        ring1
  exact (not_lt_of_ge coefficientProductStrict.le largeCoefficient).elim


/-- The first generated prefix `a₀/1`. -/
def firstStage (source : Fraction) : Stage source :=
  { quotient := source
    previous := ⟨1, 0⟩
    current := ⟨digit source, 1⟩
    unitDeterminant := by
      right
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [determinant,
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
    represents := by
      simpa only [toGaussian_one, toGaussian_zero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.mul_zero,
        RFAP.ConstructiveGaussian.Gaussian.add_zero,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
        using value_eq_digit_add_residual source }

/-- Move one stage along a nonterminal complete quotient. -/
def advanceStage {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0) : Stage source := by
  let nextQuotient := next stage.quotient nonterminal
  let nextDigit := digit nextQuotient
  let nextResidual := residual nextQuotient
  let nextCurrent := advancePair nextDigit stage.current stage.previous
  have oldResidualNonzero : residual stage.quotient ≠ 0 :=
    residual_ne_zero nonterminal
  have nextValue : nextQuotient.value =
      (residual stage.quotient)⁻¹ :=
    next_value stage.quotient nonterminal
  have reciprocal :
      nextQuotient.value * residual stage.quotient = 1 := by
    rw [nextValue, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ oldResidualNonzero]
  have nextDecomposition :
      nextQuotient.value = toGaussian nextDigit + nextResidual :=
    value_eq_digit_add_residual nextQuotient
  have scaledRepresentation := congrArg
    (fun value => nextQuotient.value * value) stage.represents
  refine
    { quotient := nextQuotient
      previous := stage.current
      current := nextCurrent
      unitDeterminant :=
        unitDeterminant_advancePair stage.unitDeterminant nextDigit
      represents := ?_ }
  change source.value *
      (toGaussian nextCurrent.denominator +
        nextResidual * toGaussian stage.current.denominator) =
    toGaussian nextCurrent.numerator +
      nextResidual * toGaussian stage.current.numerator
  dsimp only [nextCurrent, advancePair]
  simp only [toGaussian_add, toGaussian_mul]
  have denominatorRegroup :
      toGaussian nextDigit * toGaussian stage.current.denominator +
          toGaussian stage.previous.denominator +
            nextResidual * toGaussian stage.current.denominator =
        (toGaussian nextDigit + nextResidual) *
            toGaussian stage.current.denominator +
          toGaussian stage.previous.denominator := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  have numeratorRegroup :
      toGaussian nextDigit * toGaussian stage.current.numerator +
          toGaussian stage.previous.numerator +
            nextResidual * toGaussian stage.current.numerator =
        (toGaussian nextDigit + nextResidual) *
            toGaussian stage.current.numerator +
          toGaussian stage.previous.numerator := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  rw [denominatorRegroup, numeratorRegroup, ← nextDecomposition]
  calc
    source.value *
          (nextQuotient.value * toGaussian stage.current.denominator +
            toGaussian stage.previous.denominator) =
        nextQuotient.value *
          (source.value *
            (toGaussian stage.current.denominator +
              residual stage.quotient *
                toGaussian stage.previous.denominator)) := by
      calc
        source.value *
              (nextQuotient.value * toGaussian stage.current.denominator +
                toGaussian stage.previous.denominator) =
            source.value *
              (nextQuotient.value * toGaussian stage.current.denominator +
                (nextQuotient.value * residual stage.quotient) *
                  toGaussian stage.previous.denominator) := by
          rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = nextQuotient.value *
              (source.value *
                (toGaussian stage.current.denominator +
                  residual stage.quotient *
                    toGaussian stage.previous.denominator)) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
    _ = nextQuotient.value *
          (toGaussian stage.current.numerator +
            residual stage.quotient *
              toGaussian stage.previous.numerator) := scaledRepresentation
    _ = nextQuotient.value * toGaussian stage.current.numerator +
          toGaussian stage.previous.numerator := by
      calc
        nextQuotient.value *
              (toGaussian stage.current.numerator +
                residual stage.quotient *
                  toGaussian stage.previous.numerator) =
            nextQuotient.value * toGaussian stage.current.numerator +
              (nextQuotient.value * residual stage.quotient) *
                toGaussian stage.previous.numerator := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
        _ = nextQuotient.value * toGaussian stage.current.numerator +
              toGaussian stage.previous.numerator := by
          rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]

@[simp] theorem advanceStage_quotient {source : Fraction}
    (stage : Stage source) (nonterminal : remainder stage.quotient ≠ 0) :
    (advanceStage stage nonterminal).quotient =
      next stage.quotient nonterminal := by
  rfl

/-- Fuel-explicit generation of a finite Hurwitz trace.  A zero-fuel call
retains its current stage; the public constructor supplies one more unit of
fuel than the current denominator quadrance, and strict denominator descent
therefore prevents this fallback from truncating a generated trace. -/
def stagesFromFuel {source : Fraction} : Nat → Stage source → List (Stage source)
  | 0, stage => [stage]
  | fuel + 1, stage =>
      if terminal : remainder stage.quotient = 0 then
        [stage]
      else
        stage :: stagesFromFuel fuel (advanceStage stage terminal)

/-- All generated stages, ending at the terminal complete quotient. -/
def stagesFrom {source : Fraction} (stage : Stage source) :
    List (Stage source) :=
  stagesFromFuel (Nat.succ (normNat stage.quotient.denominator)) stage

/-- Complete finite trace of a displayed Gaussian rational. -/
def stages (source : Fraction) : List (Stage source) :=
  stagesFrom (firstStage source)

/-- Sufficient explicit fuel makes the generated trace contain a terminal
stage. -/
private theorem exists_terminal_mem_stagesFromFuel {source : Fraction}
    (fuel : Nat) (stage : Stage source)
    (enough : normNat stage.quotient.denominator < fuel) :
    ∃ terminalStage,
      terminalStage ∈ stagesFromFuel fuel stage ∧
        remainder terminalStage.quotient = 0 := by
  induction fuel generalizing stage with
  | zero => exact (Nat.not_lt_zero _ enough).elim
  | succ fuel inductionHypothesis =>
      by_cases terminal : remainder stage.quotient = 0
      · refine ⟨stage, ?_, terminal⟩
        simp only [stagesFromFuel, dif_pos terminal, List.mem_singleton]
      · have descent :
            normNat (advanceStage stage terminal).quotient.denominator <
              normNat stage.quotient.denominator := by
          rw [advanceStage_quotient]
          exact remainder_norm_lt_denominator stage.quotient
        have currentLeFuel :
            normNat stage.quotient.denominator ≤ fuel :=
          Nat.le_of_lt_succ enough
        have nextEnough :
            normNat (advanceStage stage terminal).quotient.denominator < fuel :=
          descent.trans_le currentLeFuel
        obtain ⟨terminalStage, member, terminalStageTerminal⟩ :=
          inductionHypothesis (advanceStage stage terminal) nextEnough
        refine ⟨terminalStage, ?_, terminalStageTerminal⟩
        simp only [stagesFromFuel, dif_neg terminal, List.mem_cons]
        exact Or.inr member

/-- Every explicitly bounded stage trace contains its terminal stage. -/
theorem exists_terminal_mem_stagesFrom {source : Fraction}
    (stage : Stage source) :
    ∃ terminalStage,
      terminalStage ∈ stagesFrom stage ∧
        remainder terminalStage.quotient = 0 := by
  exact exists_terminal_mem_stagesFromFuel
    (Nat.succ (normNat stage.quotient.denominator)) stage
      (Nat.lt_succ_self _)

/-- The executable trace of every displayed rational source is nonempty and
contains an explicitly terminal generated stage. -/
theorem exists_terminal_mem_stages (source : Fraction) :
    ∃ terminalStage,
      terminalStage ∈ stages source ∧
        remainder terminalStage.quotient = 0 :=
  exists_terminal_mem_stagesFrom (firstStage source)

end RFAP.HurwitzTrace
