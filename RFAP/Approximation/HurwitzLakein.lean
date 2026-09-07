import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzGeometry
import RFAP.Approximation.BestApproximation

/-!
# The finite Lakein inequality for Hurwitz convergents

This module closes the last exceptional coefficient case left by the elementary
Hurwitz-square geometry.  The normalized adjacent-denominator ratio is an
explicit Gaussian rational.  Its finite laws of succession keep it in
`[-3/4, 3/4]²`; that coordinate certificate excludes every quadrance-five
current coefficient paired with a diagonal previous coefficient.
-/

namespace RFAP.HurwitzGeometry

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.HurwitzRational
open RFAP.HurwitzApproximation

/-- The preceding continuant denominator divided by the current one.  This is
formed only from displayed Gaussian integers. -/
def Stage.denominatorRatio {source : Fraction} (stage : Stage source) :
    Gaussian :=
  toGaussian stage.previous.denominator *
    (toGaussian stage.current.denominator)⁻¹

@[simp] theorem firstStage_denominatorRatio (source : Fraction) :
    Stage.denominatorRatio (RFAP.HurwitzTrace.firstStage source) = 0 := by
  unfold Stage.denominatorRatio RFAP.HurwitzTrace.firstStage
  simp only [toGaussian_zero, toGaussian_one,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.inv_one_direct,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul]

/-- The finite coordinate region needed for Lakein's exceptional coefficient
case. -/
def DenominatorRatioInLakeinSquare {source : Fraction}
    (stage : Stage source) : Prop :=
  -(3 / 4 : Coordinate) ≤ stage.denominatorRatio.re ∧
    stage.denominatorRatio.re ≤ (3 / 4 : Coordinate) ∧
    -(3 / 4 : Coordinate) ≤ stage.denominatorRatio.im ∧
    stage.denominatorRatio.im ≤ (3 / 4 : Coordinate)

theorem current_denominator_ne_zero_of_generated
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) :
    stage.current.denominator ≠ 0 := by
  intro currentZero
  have growth := stage_denominatorGrowth generated
  rw [currentZero] at growth
  change normNat stage.previous.denominator < 0 at growth
  omega

theorem denominatorRatio_mul_current {source : Fraction}
    (stage : Stage source) (currentNonzero : stage.current.denominator ≠ 0) :
    stage.denominatorRatio * toGaussian stage.current.denominator =
      toGaussian stage.previous.denominator := by
  have currentGaussianNonzero :
      toGaussian stage.current.denominator ≠ 0 := by
    intro currentZero
    exact currentNonzero (toGaussian_eq_zero.mp currentZero)
  dsimp only [Stage.denominatorRatio]
  calc
    (toGaussian stage.previous.denominator *
          (toGaussian stage.current.denominator)⁻¹) *
        toGaussian stage.current.denominator =
      toGaussian stage.previous.denominator *
        ((toGaussian stage.current.denominator)⁻¹ *
          toGaussian stage.current.denominator) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = toGaussian stage.previous.denominator * 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _
          currentGaussianNonzero]
    _ = toGaussian stage.previous.denominator :=
      RFAP.ConstructiveGaussian.Gaussian.mul_one _

theorem denominatorRatio_normSq_lt_one_of_generated
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) :
    normSq stage.denominatorRatio < 1 := by
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  have currentGaussianNonzero :
      toGaussian stage.current.denominator ≠ 0 := by
    intro currentZero
    exact currentNonzero (toGaussian_eq_zero.mp currentZero)
  have currentPositive :
      0 < normSq (toGaussian stage.current.denominator) :=
    normSq_pos currentGaussianNonzero
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := normSq (toGaussian stage.current.denominator)) _ currentPositive
  calc
    normSq stage.denominatorRatio *
          normSq (toGaussian stage.current.denominator) =
        normSq
          (stage.denominatorRatio *
            toGaussian stage.current.denominator) := by
      rw [normSq_mul]
    _ = normSq (toGaussian stage.previous.denominator) := by
      rw [denominatorRatio_mul_current stage currentNonzero]
    _ = (normNat stage.previous.denominator : Coordinate) :=
      normSq_toGaussian _
    _ < (normNat stage.current.denominator : Coordinate) :=
      RFAP.ConstructiveFraction.natCast_lt_direct
        (stage_denominatorGrowth generated)
    _ = normSq (toGaussian stage.current.denominator) :=
      (normSq_toGaussian _).symm
    _ = 1 * normSq (toGaussian stage.current.denominator) := by ring1

/-- Advancing the trace applies the usual finite backward-continued-fraction
map to the displayed denominator ratio. -/
theorem advanceStage_denominatorRatio {source : Fraction}
    (stage : Stage source) (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0) :
    Stage.denominatorRatio
        (RFAP.HurwitzTrace.advanceStage stage nonterminal) =
      (toGaussian (digit (next stage.quotient nonterminal)) +
        stage.denominatorRatio)⁻¹ := by
  let advanced := RFAP.HurwitzTrace.advanceStage stage nonterminal
  let nextDigit := digit (next stage.quotient nonterminal)
  let currentValue := toGaussian stage.current.denominator
  let advancedValue := toGaussian advanced.current.denominator
  let divisor := toGaussian nextDigit + stage.denominatorRatio
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  have advancedGenerated : Generated source advanced :=
    Generated.advance generated nonterminal
  have advancedNonzero :=
    current_denominator_ne_zero_of_generated advancedGenerated
  have advancedGaussianNonzero : advancedValue ≠ 0 := by
    intro advancedZero
    exact advancedNonzero (toGaussian_eq_zero.mp advancedZero)
  have divisorMulCurrent : divisor * currentValue = advancedValue := by
    dsimp only [divisor, currentValue, advancedValue, advanced, nextDigit]
    change
      (toGaussian (digit (next stage.quotient nonterminal)) +
          stage.denominatorRatio) *
          toGaussian stage.current.denominator =
        toGaussian
          (digit (next stage.quotient nonterminal) *
            stage.current.denominator + stage.previous.denominator)
    rw [toGaussian_add, toGaussian_mul,
      ← denominatorRatio_mul_current stage currentNonzero]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  have divisorNonzero : divisor ≠ 0 := by
    intro divisorZero
    have zeroAdvanced : advancedValue = 0 := by
      rw [← divisorMulCurrent, divisorZero,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul]
    exact advancedGaussianNonzero zeroAdvanced
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    advancedGaussianNonzero
  calc
    Stage.denominatorRatio advanced * advancedValue =
        toGaussian advanced.previous.denominator :=
      denominatorRatio_mul_current advanced advancedNonzero
    _ = currentValue := rfl
    _ = 1 * currentValue := by
      rw [RFAP.ConstructiveGaussian.Gaussian.one_mul]
    _ = (divisor⁻¹ * divisor) * currentValue := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ divisorNonzero]
    _ = divisor⁻¹ * (divisor * currentValue) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = divisor⁻¹ * advancedValue := by rw [divisorMulCurrent]
    _ = (toGaussian (digit (next stage.quotient nonterminal)) +
          stage.denominatorRatio)⁻¹ * advancedValue := rfl

private theorem twice_lt_one_of_lt_half {value : Coordinate}
    (upper : value < 1 / 2) : 2 * value < 1 := by
  have scaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 2 by decide) upper
  calc
    2 * value < 2 * (1 / 2 : Coordinate) := scaled
    _ = 1 := by decide

private theorem half_two_mul (value : Coordinate) :
    (1 / 2 : Coordinate) * (2 * value) = value := by
  calc
    (1 / 2 : Coordinate) * (2 * value) =
        ((1 / 2 : Coordinate) + 1 / 2) * value := by ring1
    _ = 1 * value := by rw [show
      (1 / 2 : Coordinate) + 1 / 2 = 1 by decide]
    _ = value := RFAP.ConstructiveFraction.one_mul value

/-- The half-open tie convention makes the exterior test at `1` strict.
This is the one strict edge needed by the finite succession table. -/
theorem one_lt_next_sub_one_normSq (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) :
    1 < normSq ((next fraction nonterminal).value - 1) := by
  let rho := residual fraction
  let nextValue := (next fraction nonterminal).value
  have rhoNonzero : rho ≠ 0 := residual_ne_zero nonterminal
  have rhoPositive : 0 < normSq rho := normSq_pos rhoNonzero
  have reciprocal : nextValue * rho = 1 := by
    dsimp only [nextValue, rho]
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ rhoNonzero]
  have factorIdentity : (nextValue - 1) * rho = 1 - rho := by
    calc
      (nextValue - 1) * rho = nextValue * rho - 1 * rho := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = 1 - rho := by
        rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem fraction.value
  have gapPositive : 0 < 1 - 2 * rho.re := by
    exact RFAP.ConstructiveFraction.sub_pos_direct
      (twice_lt_one_of_lt_half rhoSquare.2.1)
  have residualStrict : normSq rho < normSq (1 - rho) := by
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct
        gapPositive (normSq rho)
    calc
      normSq rho = normSq rho + 0 := by ring1
      _ < normSq rho + (1 - 2 * rho.re) := shifted
      _ = normSq (1 - rho) := by
        simp only [normSq,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im]
        ring1
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := normSq rho) _ rhoPositive
  calc
    1 * normSq rho = normSq rho := by ring1
    _ < normSq (1 - rho) := residualStrict
    _ = normSq ((nextValue - 1) * rho) := by rw [factorIdentity]
    _ = normSq (nextValue - 1) * normSq rho := normSq_mul _ _

private theorem next_value_real_lower_of_one_add_i_digit
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨1, 1⟩) :
    -(1 / 2 : Coordinate) ≤
      (next (next fraction nonterminal) nextNonterminal).value.re := by
  let current := next fraction nonterminal
  let following := next current nextNonterminal
  let rho := residual current
  have rhoNonzero : rho ≠ 0 := residual_ne_zero nextNonterminal
  have rhoPositive : 0 < normSq rho := normSq_pos rhoNonzero
  have currentDecomposition :
      current.value = toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
    calc
      current.value = toGaussian (digit current) + residual current :=
        value_eq_digit_add_residual current
      _ = toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
        rw [digitValue]
  have exterior := one_le_next_sub_unit_normSq fraction nonterminal
    (unit := imaginaryUnit) (Or.inr (Or.inr (Or.inl rfl)))
  have scaledLower : -(1 / 2 : Coordinate) * normSq rho ≤ rho.re := by
    rw [currentDecomposition] at exterior
    simp only [normSq, imaginaryUnit, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      Int.cast_zero, Int.cast_one] at exterior
    have doubled : -normSq rho ≤ 2 * rho.re := by
      have shifted :=
        RFAP.ConstructiveFraction.add_le_add_right_direct exterior (-1)
      have nonnegative : 0 ≤ normSq rho + 2 * rho.re := by
        calc
          0 = (1 : Coordinate) + -1 := by ring1
          _ ≤ ((1 + rho.re - 0) ^ 2 +
                (1 + rho.im - 1) ^ 2) + -1 := shifted
          _ = normSq rho + 2 * rho.re := by
            dsimp only [normSq]
            ring1
      have translated :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          nonnegative (-normSq rho)
      calc
        -normSq rho = 0 + -normSq rho := by ring1
        _ ≤ (normSq rho + 2 * rho.re) + -normSq rho := translated
        _ = 2 * rho.re := by ring1
    have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := by decide
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        doubled halfNonnegative
    calc
      -(1 / 2 : Coordinate) * normSq rho =
          (1 / 2 : Coordinate) * (-normSq rho) := by ring1
      _ ≤ (1 / 2 : Coordinate) * (2 * rho.re) := scaled
      _ = rho.re := half_two_mul rho.re
  have divided :=
    (RFAP.ConstructiveFraction.le_div_iff_pos rhoPositive).2 scaledLower
  rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq]
  change -(1 / 2 : Coordinate) ≤ rho.re / normSq rho
  exact divided

private theorem next_value_imaginary_upper_of_one_add_i_digit
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨1, 1⟩) :
    (next (next fraction nonterminal) nextNonterminal).value.im <
      (1 / 2 : Coordinate) := by
  let current := next fraction nonterminal
  let following := next current nextNonterminal
  let rho := residual current
  have rhoNonzero : rho ≠ 0 := residual_ne_zero nextNonterminal
  have rhoPositive : 0 < normSq rho := normSq_pos rhoNonzero
  have currentDecomposition :
      current.value = toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
    calc
      current.value = toGaussian (digit current) + residual current :=
        value_eq_digit_add_residual current
      _ = toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
        rw [digitValue]
  have exterior := one_lt_next_sub_one_normSq fraction nonterminal
  have scaledUpper : -rho.im < (1 / 2 : Coordinate) * normSq rho := by
    rw [currentDecomposition] at exterior
    simp only [normSq, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im,
      Int.cast_one] at exterior
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct exterior (-1)
    have positive : 0 < normSq rho + 2 * rho.im := by
      calc
        0 = (1 : Coordinate) + -1 := by ring1
        _ < ((1 + rho.re - 1) ^ 2 +
              (1 + rho.im - 0) ^ 2) + -1 := shifted
        _ = normSq rho + 2 * rho.im := by
          dsimp only [normSq]
          ring1
    have translated :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        positive (-(2 * rho.im))
    have doubled : -(2 * rho.im) < normSq rho := by
      calc
        -(2 * rho.im) = 0 + -(2 * rho.im) := by ring1
        _ < (normSq rho + 2 * rho.im) + -(2 * rho.im) := translated
        _ = normSq rho := by ring1
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (show (0 : Coordinate) < 1 / 2 by decide) doubled
    calc
      -rho.im = (1 / 2 : Coordinate) * (2 * (-rho.im)) := by
        rw [half_two_mul]
      _ = (1 / 2 : Coordinate) * (-(2 * rho.im)) := by
        congr 1
        ring1
      _ < (1 / 2 : Coordinate) * normSq rho := scaled
  have divided :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos rhoPositive).2 scaledUpper
  rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq]
  change (-rho.im) / normSq rho < (1 / 2 : Coordinate)
  exact divided

/-- A digit `1+i` can only be followed by a digit in the southeast
quadrant.  The statement includes the deterministic boundary convention. -/
theorem successor_signs_of_one_add_i
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨1, 1⟩) :
    0 ≤ (digit (next (next fraction nonterminal) nextNonterminal)).re ∧
      (digit (next (next fraction nonterminal) nextNonterminal)).im ≤ 0 := by
  let following := next (next fraction nonterminal) nextNonterminal
  let followingDigit := digit following
  let followingResidual := residual following
  have decomposition :
      following.value = toGaussian followingDigit + followingResidual :=
    value_eq_digit_add_residual following
  have residualSquare := RFAP.HurwitzNearest.remainder_mem following.value
  constructor
  · apply Int.le_of_not_gt
    intro negative
    change followingDigit.re < 0 at negative
    have digitAtMostMinusOne : followingDigit.re ≤ -1 := by omega
    have castDigitAtMostMinusOne :
        (followingDigit.re : Coordinate) ≤ -1 :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).2
        digitAtMostMinusOne
    have valueStrict : following.value.re < -(1 / 2 : Coordinate) := by
      have first := RFAP.ConstructiveFraction.add_le_add_right_direct
        castDigitAtMostMinusOne followingResidual.re
      have second := RFAP.ConstructiveFraction.add_lt_add_left_direct
        residualSquare.2.1 (-1)
      have shifted := first.trans_lt second
      calc
        following.value.re =
            (followingDigit.re : Coordinate) + followingResidual.re := by
          exact congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
        _ < (-1 : Coordinate) + 1 / 2 := shifted
        _ = -(1 / 2 : Coordinate) := by decide
    exact (not_lt_of_ge
      (next_value_real_lower_of_one_add_i_digit fraction nonterminal
        nextNonterminal digitValue) valueStrict)
  · apply Int.le_of_not_gt
    intro positive
    change 0 < followingDigit.im at positive
    have oneLeDigit : 1 ≤ followingDigit.im := by omega
    have oneLeCast : (1 : Coordinate) ≤
        (followingDigit.im : Coordinate) :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).2
        oneLeDigit
    have valueLower : (1 / 2 : Coordinate) ≤ following.value.im := by
      have first := RFAP.ConstructiveFraction.add_le_add_right_direct
        oneLeCast followingResidual.im
      have second := RFAP.ConstructiveFraction.add_le_add_right_direct
        residualSquare.2.2.1 1
      have shifted :
          (1 : Coordinate) + -(1 / 2 : Coordinate) ≤
            (followingDigit.im : Coordinate) + followingResidual.im := by
        calc
          (1 : Coordinate) + -(1 / 2 : Coordinate) =
              -(1 / 2 : Coordinate) + 1 := by ring1
          _ ≤ followingResidual.im + 1 := second
          _ = 1 + followingResidual.im := by ring1
          _ ≤ (followingDigit.im : Coordinate) + followingResidual.im := first
      calc
        (1 / 2 : Coordinate) = 1 + -(1 / 2 : Coordinate) := by decide
        _ ≤ (followingDigit.im : Coordinate) + followingResidual.im := shifted
        _ = following.value.im :=
          (congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition).symm
    exact (not_le_of_gt
      (next_value_imaginary_upper_of_one_add_i_digit fraction nonterminal
        nextNonterminal digitValue) valueLower)

/-- Clearing the following complete quotient turns a unit-disc exterior
condition into a polynomial inequality in the following residual.  This is
the common finite calculation behind the exceptional successor exclusions. -/
theorem successor_exterior_cleared
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (unit : GaussianInt) (unitProperty : IsGaussianUnit unit) :
    normSq (next (next fraction nonterminal) nextNonterminal).value ≤
      normSq
        ((toGaussian (digit (next fraction nonterminal)) - toGaussian unit) *
            (next (next fraction nonterminal) nextNonterminal).value + 1) := by
  let current := next fraction nonterminal
  let following := next current nextNonterminal
  let rho := residual current
  have rhoNonzero : rho ≠ 0 := residual_ne_zero nextNonterminal
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have productZero := congrArg (fun value => value * rho) followingZero
    rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul] at productZero
    have reciprocal : following.value * rho = 1 := by
      dsimp only [following, current, rho]
      rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ rhoNonzero]
    rw [reciprocal] at productZero
    exact (show (1 : Gaussian) ≠ 0 by decide) productZero
  have followingPositive : 0 < normSq following.value :=
    normSq_pos followingNonzero
  have exterior :
      1 ≤ normSq (current.value - toGaussian unit) := by
    dsimp only [current]
    exact one_le_next_sub_unit_normSq fraction nonterminal unitProperty
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      exterior followingPositive.le
  have reciprocal : following.value * rho = 1 := by
    dsimp only [following, current, rho]
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ rhoNonzero]
  have reciprocalReordered : rho * following.value = 1 := by
    calc
      rho * following.value = following.value * rho :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      _ = 1 := reciprocal
  have factorIdentity :
      (current.value - toGaussian unit) * following.value =
        (toGaussian (digit current) - toGaussian unit) * following.value + 1 := by
    rw [value_eq_digit_add_residual current]
    calc
      (toGaussian (digit current) + residual current - toGaussian unit) *
            following.value =
          (toGaussian (digit current) - toGaussian unit) * following.value +
            residual current * following.value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = (toGaussian (digit current) - toGaussian unit) * following.value +
          1 := by
        change (toGaussian (digit current) - toGaussian unit) *
            following.value + rho * following.value = _
        rw [reciprocalReordered]
  change normSq following.value ≤
    normSq
      ((toGaussian (digit current) - toGaussian unit) * following.value + 1)
  calc
    normSq following.value = 1 * normSq following.value := by ring1
    _ ≤ normSq (current.value - toGaussian unit) *
          normSq following.value := scaled
    _ = normSq ((current.value - toGaussian unit) * following.value) := by
      rw [normSq_mul]
    _ = normSq
        ((toGaussian (digit current) - toGaussian unit) * following.value + 1) :=
      by rw [factorIdentity]

/-- The same clearing calculation retains the strict exterior inequality at
the positive real unit. -/
theorem successor_strict_exterior_cleared
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0) :
    normSq (next (next fraction nonterminal) nextNonterminal).value <
      normSq
        ((toGaussian (digit (next fraction nonterminal)) - 1) *
            (next (next fraction nonterminal) nextNonterminal).value + 1) := by
  let current := next fraction nonterminal
  let following := next current nextNonterminal
  let rho := residual current
  have rhoNonzero : rho ≠ 0 := residual_ne_zero nextNonterminal
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have productZero := congrArg (fun value => value * rho) followingZero
    rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul] at productZero
    have reciprocal : following.value * rho = 1 := by
      dsimp only [following, current, rho]
      rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ rhoNonzero]
    rw [reciprocal] at productZero
    exact (show (1 : Gaussian) ≠ 0 by decide) productZero
  have followingPositive : 0 < normSq following.value :=
    normSq_pos followingNonzero
  have exterior : 1 < normSq (current.value - 1) := by
    dsimp only [current]
    exact one_lt_next_sub_one_normSq fraction nonterminal
  have scaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      exterior followingPositive
  have reciprocal : following.value * rho = 1 := by
    dsimp only [following, current, rho]
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ rhoNonzero]
  have reciprocalReordered : rho * following.value = 1 := by
    calc
      rho * following.value = following.value * rho :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      _ = 1 := reciprocal
  have factorIdentity :
      (current.value - 1) * following.value =
        (toGaussian (digit current) - 1) * following.value + 1 := by
    rw [value_eq_digit_add_residual current]
    calc
      (toGaussian (digit current) + residual current - 1) *
            following.value =
          (toGaussian (digit current) - 1) * following.value +
            residual current * following.value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      _ = (toGaussian (digit current) - 1) * following.value + 1 := by
        change (toGaussian (digit current) - 1) * following.value +
            rho * following.value = _
        rw [reciprocalReordered]
  change normSq following.value <
    normSq ((toGaussian (digit current) - 1) * following.value + 1)
  calc
    normSq following.value = 1 * normSq following.value := by ring1
    _ < normSq (current.value - 1) * normSq following.value := scaled
    _ = normSq ((current.value - 1) * following.value) := by
      rw [normSq_mul]
    _ = normSq
        ((toGaussian (digit current) - 1) * following.value + 1) := by
      rw [factorIdentity]

private theorem quarter_add_square_lt_twice_of_half_interval
    (value : Coordinate) (lower : (1 / 2 : Coordinate) ≤ value)
    (upper : value ≤ (3 / 2 : Coordinate)) :
    (1 / 2 : Coordinate) ^ 2 + value ^ 2 < 2 * value := by
  let displacement := value - 1
  have displacementLower : -(1 / 2 : Coordinate) ≤ displacement := by
    calc
      -(1 / 2 : Coordinate) = (1 / 2 : Coordinate) - 1 := by decide
      _ ≤ value - 1 := RFAP.ConstructiveFraction.sub_le_sub_right_direct lower 1
      _ = displacement := rfl
  have displacementUpper : displacement ≤ (1 / 2 : Coordinate) := by
    calc
      displacement = value - 1 := rfl
      _ ≤ (3 / 2 : Coordinate) - 1 := RFAP.ConstructiveFraction.sub_le_sub_right_direct upper 1
      _ = 1 / 2 := by decide
  have leftFactorNonnegative :
      0 ≤ (1 / 2 : Coordinate) - displacement :=
    RFAP.ConstructiveFraction.sub_nonneg_direct displacementUpper
  have rightFactorNonnegative :
      0 ≤ (1 / 2 : Coordinate) + displacement := by
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      displacementLower (1 / 2 : Coordinate)
    calc
      0 = -(1 / 2 : Coordinate) + 1 / 2 := by ring1
      _ ≤ displacement + 1 / 2 := shifted
      _ = 1 / 2 + displacement := by ring1
  have productNonnegative :
      0 ≤ ((1 / 2 : Coordinate) - displacement) *
        ((1 / 2 : Coordinate) + displacement) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      leftFactorNonnegative rightFactorNonnegative
  have displacementSquareUpper :
      displacement ^ 2 ≤ (1 / 4 : Coordinate) := by
    have gap : 0 ≤ (1 / 4 : Coordinate) - displacement ^ 2 := by
      calc
        0 ≤ ((1 / 2 : Coordinate) - displacement) *
            ((1 / 2 : Coordinate) + displacement) := productNonnegative
        _ = (1 / 2 : Coordinate) * (1 / 2) - displacement ^ 2 := by
          ring1
        _ = (1 / 4 : Coordinate) - displacement ^ 2 := by
          rw [show (1 / 2 : Coordinate) * (1 / 2) = 1 / 4 by decide]
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct gap
  have differenceUpper :
      (1 / 2 : Coordinate) ^ 2 + value ^ 2 - 2 * value ≤
        -(1 / 2 : Coordinate) := by
    calc
      (1 / 2 : Coordinate) ^ 2 + value ^ 2 - 2 * value =
          displacement ^ 2 - (1 - (1 / 2 : Coordinate) ^ 2) := by
        dsimp only [displacement]
        ring1
      _ = displacement ^ 2 - 3 / 4 := by
        rw [show (1 : Coordinate) - (1 / 2) ^ 2 = 3 / 4 by decide]
      _ ≤ (1 / 4 : Coordinate) - 3 / 4 :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct
          displacementSquareUpper (3 / 4 : Coordinate)
      _ = -(1 / 2 : Coordinate) := by decide
  have differenceNegative :
      (1 / 2 : Coordinate) ^ 2 + value ^ 2 - 2 * value < 0 :=
    differenceUpper.trans_lt (show -(1 / 2 : Coordinate) < 0 by decide)
  exact RFAP.ConstructiveFraction.lt_of_sub_neg_direct differenceNegative

/-- A residual can be recovered from the following displayed quotient by
one finite inversion; no infinite tail is involved. -/
theorem residual_eq_next_value_inv (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) :
    residual fraction = (next fraction nonterminal).value⁻¹ := by
  let rho := residual fraction
  let following := next fraction nonterminal
  have rhoNonzero : rho ≠ 0 := residual_ne_zero nonterminal
  have reciprocal : following.value * rho = 1 := by
    dsimp only [following, rho]
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ rhoNonzero]
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    rw [followingZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul] at reciprocal
    exact (show (1 : Gaussian) ≠ 0 by decide) reciprocal.symm
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    followingNonzero
  calc
    residual fraction * following.value = following.value * rho := by
      dsimp only [rho]
      exact RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
    _ = 1 := reciprocal
    _ = following.value⁻¹ * following.value := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ followingNonzero]
    _ = (next fraction nonterminal).value⁻¹ * following.value := rfl

private theorem next_residual_real_lower_strict_of_one_add_i
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨1, 1⟩) :
    -(1 / 2 : Coordinate) < (residual (next fraction nonterminal)).re := by
  let following := next fraction nonterminal
  let sigma := residual following
  have sigmaSquare := RFAP.HurwitzNearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.re = -(1 / 2 : Coordinate) :=
    le_antisymm upper sigmaSquare.1
  have decomposition :
      following.value = toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by
    calc
      following.value = toGaussian (digit following) + residual following :=
        value_eq_digit_add_residual following
      _ = toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have realValue : following.value.re = (1 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_re,
      Int.cast_one] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.re = 1 + -(1 / 2 : Coordinate) := component
      _ = 1 / 2 := by decide
  have imaginaryLower : (1 / 2 : Coordinate) ≤ following.value.im := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_im,
      Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.2.2.1 1
    calc
      (1 / 2 : Coordinate) = -(1 / 2 : Coordinate) + 1 := by decide
      _ ≤ sigma.im + 1 := shifted
      _ = 1 + sigma.im := by ring1
      _ = following.value.im := component.symm
  have imaginaryUpper : following.value.im ≤ (3 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_im,
      Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.2.2.2.le 1
    calc
      following.value.im = 1 + sigma.im := component
      _ = sigma.im + 1 := by ring1
      _ ≤ (1 / 2 : Coordinate) + 1 := shifted
      _ = 3 / 2 := by decide
  have normLess : normSq following.value < 2 * following.value.im := by
    rw [normSq, realValue]
    exact quarter_add_square_lt_twice_of_half_interval following.value.im
      imaginaryLower imaginaryUpper
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := next_normSq_ge_two fraction nonterminal
    rw [followingZero, normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Coordinate) < 2 by decide)) lower
  have normPositive : 0 < normSq following.value := normSq_pos followingNonzero
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (show (0 : Coordinate) < 1 / 2 by decide) normLess
  have numeratorStrict :
      -following.value.im <
        -(1 / 2 : Coordinate) * normSq following.value := by
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct scaled
    calc
      -following.value.im = -((1 / 2 : Coordinate) *
          (2 * following.value.im)) := by
        rw [half_two_mul]
      _ < -((1 / 2 : Coordinate) * normSq following.value) := negated
      _ = -(1 / 2 : Coordinate) * normSq following.value := by ring1
  have quotientStrict :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos normPositive).2 numeratorStrict
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem fraction.value
  change RFAP.HurwitzNearest.InFundamentalSquare (residual fraction)
    at rhoSquare
  have rhoLower := rhoSquare.2.2.1
  change -(1 / 2 : Coordinate) ≤ (residual fraction).im at rhoLower
  rw [residual_eq_next_value_inv fraction nonterminal,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq] at rhoLower
  change -(1 / 2 : Coordinate) ≤
    -following.value.im / normSq following.value at rhoLower
  exact (not_lt_of_ge rhoLower quotientStrict)

private theorem next_residual_real_lower_strict_of_one_sub_i
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨1, -1⟩) :
    -(1 / 2 : Coordinate) < (residual (next fraction nonterminal)).re := by
  let following := next fraction nonterminal
  let sigma := residual following
  have sigmaSquare := RFAP.HurwitzNearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.re = -(1 / 2 : Coordinate) :=
    le_antisymm upper sigmaSquare.1
  have decomposition :
      following.value = toGaussian (⟨1, -1⟩ : GaussianInt) + sigma := by
    calc
      following.value = toGaussian (digit following) + residual following :=
        value_eq_digit_add_residual following
      _ = toGaussian (⟨1, -1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have realValue : following.value.re = (1 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_re,
      Int.cast_one] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.re = 1 + -(1 / 2 : Coordinate) := component
      _ = 1 / 2 := by decide
  let magnitude := -following.value.im
  have magnitudeLower : (1 / 2 : Coordinate) ≤ magnitude := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_im,
      Int.cast_neg, Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.2.2.2.le (-1)
    have followingUpper : following.value.im ≤ -(1 / 2 : Coordinate) := by
      calc
        following.value.im = (-1 : Coordinate) + sigma.im := component
        _ = sigma.im + (-1 : Coordinate) := by ring1
        _ ≤ (1 / 2 : Coordinate) + (-1 : Coordinate) := shifted
        _ = -(1 / 2 : Coordinate) := by decide
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct followingUpper
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have magnitudeUpper : magnitude ≤ (3 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_im,
      Int.cast_neg, Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.2.2.1 (-1)
    have followingLower : -(3 / 2 : Coordinate) ≤ following.value.im := by
      calc
        -(3 / 2 : Coordinate) = -(1 / 2 : Coordinate) + (-1) := by decide
        _ ≤ sigma.im + (-1 : Coordinate) := shifted
        _ = (-1 : Coordinate) + sigma.im := by ring1
        _ = following.value.im := component.symm
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct followingLower
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have normLess : normSq following.value < 2 * magnitude := by
    rw [normSq, realValue]
    have bound := quarter_add_square_lt_twice_of_half_interval magnitude
      magnitudeLower magnitudeUpper
    convert bound using 1
    all_goals dsimp only [magnitude]
    all_goals ring1
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := next_normSq_ge_two fraction nonterminal
    rw [followingZero, normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Coordinate) < 2 by decide)) lower
  have normPositive : 0 < normSq following.value := normSq_pos followingNonzero
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (show (0 : Coordinate) < 1 / 2 by decide) normLess
  have lowerQuotient :
      (1 / 2 : Coordinate) < magnitude / normSq following.value :=
    (RFAP.ConstructiveFraction.lt_div_iff_pos normPositive).2 (by
      calc
        (1 / 2 : Coordinate) * normSq following.value <
            (1 / 2 : Coordinate) * (2 * magnitude) := scaled
        _ = magnitude := half_two_mul magnitude)
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem fraction.value
  change RFAP.HurwitzNearest.InFundamentalSquare (residual fraction)
    at rhoSquare
  have rhoUpper := rhoSquare.2.2.2
  change (residual fraction).im < (1 / 2 : Coordinate) at rhoUpper
  rw [residual_eq_next_value_inv fraction nonterminal,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq] at rhoUpper
  change
    -following.value.im / normSq following.value < (1 / 2 : Coordinate)
      at rhoUpper
  have quotientIdentity :
      -following.value.im / normSq following.value =
        magnitude / normSq following.value := by rfl
  rw [quotientIdentity] at rhoUpper
  exact (not_lt_of_ge lowerQuotient.le rhoUpper)

private theorem next_residual_imaginary_lower_strict_of_one_add_i
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨1, 1⟩) :
    -(1 / 2 : Coordinate) < (residual (next fraction nonterminal)).im := by
  let following := next fraction nonterminal
  let sigma := residual following
  have sigmaSquare := RFAP.HurwitzNearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.im = -(1 / 2 : Coordinate) :=
    le_antisymm upper sigmaSquare.2.2.1
  have decomposition :
      following.value = toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by
    calc
      following.value = toGaussian (digit following) + residual following :=
        value_eq_digit_add_residual following
      _ = toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have imaginaryValue : following.value.im = (1 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_im,
      Int.cast_one] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.im = 1 + -(1 / 2 : Coordinate) := component
      _ = 1 / 2 := by decide
  have realLower : (1 / 2 : Coordinate) ≤ following.value.re := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_re,
      Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.1 1
    calc
      (1 / 2 : Coordinate) = -(1 / 2 : Coordinate) + 1 := by decide
      _ ≤ sigma.re + 1 := shifted
      _ = 1 + sigma.re := by ring1
      _ = following.value.re := component.symm
  have realUpper : following.value.re ≤ (3 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_re,
      Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.2.1.le 1
    calc
      following.value.re = 1 + sigma.re := component
      _ = sigma.re + 1 := by ring1
      _ ≤ (1 / 2 : Coordinate) + 1 := shifted
      _ = 3 / 2 := by decide
  have normLess : normSq following.value < 2 * following.value.re := by
    rw [normSq, imaginaryValue]
    calc
      following.value.re ^ 2 + (1 / 2 : Coordinate) ^ 2 =
          (1 / 2 : Coordinate) ^ 2 + following.value.re ^ 2 := by ring1
      _ < 2 * following.value.re :=
        quarter_add_square_lt_twice_of_half_interval following.value.re
          realLower realUpper
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := next_normSq_ge_two fraction nonterminal
    rw [followingZero, normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Coordinate) < 2 by decide)) lower
  have normPositive : 0 < normSq following.value := normSq_pos followingNonzero
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (show (0 : Coordinate) < 1 / 2 by decide) normLess
  have quotientStrict :
      (1 / 2 : Coordinate) <
        following.value.re / normSq following.value :=
    (RFAP.ConstructiveFraction.lt_div_iff_pos normPositive).2 (by
      calc
        (1 / 2 : Coordinate) * normSq following.value <
            (1 / 2 : Coordinate) * (2 * following.value.re) := scaled
        _ = following.value.re := half_two_mul following.value.re)
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem fraction.value
  change RFAP.HurwitzNearest.InFundamentalSquare (residual fraction)
    at rhoSquare
  have rhoUpper := rhoSquare.2.1
  change (residual fraction).re < (1 / 2 : Coordinate) at rhoUpper
  rw [residual_eq_next_value_inv fraction nonterminal,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq] at rhoUpper
  change following.value.re / normSq following.value <
    (1 / 2 : Coordinate) at rhoUpper
  exact (not_lt_of_ge quotientStrict.le rhoUpper)

private theorem next_residual_imaginary_lower_strict_of_neg_one_add_i
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (digitValue : digit (next fraction nonterminal) = ⟨-1, 1⟩) :
    -(1 / 2 : Coordinate) < (residual (next fraction nonterminal)).im := by
  let following := next fraction nonterminal
  let sigma := residual following
  have sigmaSquare := RFAP.HurwitzNearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.im = -(1 / 2 : Coordinate) :=
    le_antisymm upper sigmaSquare.2.2.1
  have decomposition :
      following.value = toGaussian (⟨-1, 1⟩ : GaussianInt) + sigma := by
    calc
      following.value = toGaussian (digit following) + residual following :=
        value_eq_digit_add_residual following
      _ = toGaussian (⟨-1, 1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have imaginaryValue : following.value.im = (1 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_im,
      Int.cast_one] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.im = 1 + -(1 / 2 : Coordinate) := component
      _ = 1 / 2 := by decide
  let magnitude := -following.value.re
  have magnitudeLower : (1 / 2 : Coordinate) ≤ magnitude := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_re,
      Int.cast_neg, Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.2.1.le (-1)
    have followingUpper : following.value.re ≤ -(1 / 2 : Coordinate) := by
      calc
        following.value.re = (-1 : Coordinate) + sigma.re := component
        _ = sigma.re + (-1 : Coordinate) := by ring1
        _ ≤ (1 / 2 : Coordinate) + (-1 : Coordinate) := shifted
        _ = -(1 / 2 : Coordinate) := by decide
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct followingUpper
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have magnitudeUpper : magnitude ≤ (3 / 2 : Coordinate) := by
    have component := congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
    simp only [toGaussian, RFAP.ConstructiveGaussian.Gaussian.add_re,
      Int.cast_neg, Int.cast_one] at component
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      sigmaSquare.1 (-1)
    have followingLower : -(3 / 2 : Coordinate) ≤ following.value.re := by
      calc
        -(3 / 2 : Coordinate) = -(1 / 2 : Coordinate) + (-1) := by decide
        _ ≤ sigma.re + (-1 : Coordinate) := shifted
        _ = (-1 : Coordinate) + sigma.re := by ring1
        _ = following.value.re := component.symm
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct followingLower
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have normLess : normSq following.value < 2 * magnitude := by
    rw [normSq, imaginaryValue]
    have bound := quarter_add_square_lt_twice_of_half_interval magnitude
      magnitudeLower magnitudeUpper
    convert bound using 1
    all_goals dsimp only [magnitude]
    all_goals ring1
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := next_normSq_ge_two fraction nonterminal
    rw [followingZero, normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Coordinate) < 2 by decide)) lower
  have normPositive : 0 < normSq following.value := normSq_pos followingNonzero
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (show (0 : Coordinate) < 1 / 2 by decide) normLess
  have numeratorStrict :
      following.value.re <
        -(1 / 2 : Coordinate) * normSq following.value := by
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct scaled
    calc
      following.value.re = -magnitude := by dsimp only [magnitude]; ring1
      _ = -((1 / 2 : Coordinate) * (2 * magnitude)) := by
        rw [half_two_mul]
      _ < -((1 / 2 : Coordinate) * normSq following.value) := negated
      _ = -(1 / 2 : Coordinate) * normSq following.value := by ring1
  have quotientStrict :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos normPositive).2 numeratorStrict
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem fraction.value
  change RFAP.HurwitzNearest.InFundamentalSquare (residual fraction)
    at rhoSquare
  have rhoLower := rhoSquare.1
  change -(1 / 2 : Coordinate) ≤ (residual fraction).re at rhoLower
  rw [residual_eq_next_value_inv fraction nonterminal,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq] at rhoLower
  change -(1 / 2 : Coordinate) ≤
    following.value.re / normSq following.value at rhoLower
  exact (not_lt_of_ge rhoLower quotientStrict)

/-- The signed quadrance difference obtained after clearing one proposed
adjacent digit pair against a Gaussian-unit exterior disc. -/
def successorGap (previousDigit followingDigit unit : GaussianInt)
    (followingResidual : Gaussian) : Coordinate :=
  normSq
      ((toGaussian previousDigit - toGaussian unit) *
          (toGaussian followingDigit + followingResidual) + 1) -
    normSq (toGaussian followingDigit + followingResidual)

private theorem successor_pair_false_of_negative_gap
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (previousDigit followingDigit unit : GaussianInt)
    (unitProperty : IsGaussianUnit unit)
    (previousDigitValue : digit (next fraction nonterminal) = previousDigit)
    (followingDigitValue :
      digit (next (next fraction nonterminal) nextNonterminal) = followingDigit)
    (negativeGap :
      successorGap previousDigit followingDigit unit
        (residual (next (next fraction nonterminal) nextNonterminal)) < 0) :
    False := by
  let following := next (next fraction nonterminal) nextNonterminal
  have decomposition :
      following.value =
        toGaussian followingDigit + residual following := by
    calc
      following.value = toGaussian (digit following) + residual following :=
        value_eq_digit_add_residual following
      _ = toGaussian followingDigit + residual following := by
        rw [followingDigitValue]
  have exterior := successor_exterior_cleared fraction nonterminal
    nextNonterminal unit unitProperty
  rw [previousDigitValue, decomposition] at exterior
  have strictGap :
      normSq
          ((toGaussian previousDigit - toGaussian unit) *
              (toGaussian followingDigit + residual following) + 1) <
        normSq (toGaussian followingDigit + residual following) :=
    RFAP.ConstructiveFraction.lt_of_sub_neg_direct (by
      change successorGap previousDigit followingDigit unit
        (residual following) < 0
      exact negativeGap)
  exact (not_lt_of_ge exterior strictGap)

private theorem successor_pair_false_of_nonpositive_gap_at_one
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (previousDigit followingDigit : GaussianInt)
    (previousDigitValue : digit (next fraction nonterminal) = previousDigit)
    (followingDigitValue :
      digit (next (next fraction nonterminal) nextNonterminal) = followingDigit)
    (nonpositiveGap :
      successorGap previousDigit followingDigit 1
        (residual (next (next fraction nonterminal) nextNonterminal)) ≤ 0) :
    False := by
  let following := next (next fraction nonterminal) nextNonterminal
  have decomposition :
      following.value =
        toGaussian followingDigit + residual following := by
    calc
      following.value = toGaussian (digit following) + residual following :=
        value_eq_digit_add_residual following
      _ = toGaussian followingDigit + residual following := by
        rw [followingDigitValue]
  have exterior := successor_strict_exterior_cleared fraction nonterminal
    nextNonterminal
  rw [previousDigitValue, decomposition] at exterior
  have weakGap :
      normSq
          ((toGaussian previousDigit - 1) *
              (toGaussian followingDigit + residual following) + 1) ≤
        normSq (toGaussian followingDigit + residual following) :=
    sub_nonpos.mp (by
      change successorGap previousDigit followingDigit 1
        (residual following) ≤ 0
      exact nonpositiveGap)
  exact (not_lt_of_ge weakGap exterior)

/-- The twenty-eight small adjacent digit pairs left by the two-step
Hermitian calculation.  Constructors are finite displayed data, so
elimination of the relation is kernel-checked case analysis. -/
inductive ForbiddenSmallSuccessor : GaussianInt → GaussianInt → Prop
  | c01 : ForbiddenSmallSuccessor ⟨-2, -1⟩ ⟨1, -1⟩
  | c02 : ForbiddenSmallSuccessor ⟨-2, 0⟩ ⟨1, -1⟩
  | c03 : ForbiddenSmallSuccessor ⟨-2, 0⟩ ⟨1, 1⟩
  | c04 : ForbiddenSmallSuccessor ⟨-2, 1⟩ ⟨1, 1⟩
  | c05 : ForbiddenSmallSuccessor ⟨-1, -2⟩ ⟨1, -1⟩
  | c06 : ForbiddenSmallSuccessor ⟨-1, -1⟩ ⟨0, -2⟩
  | c07 : ForbiddenSmallSuccessor ⟨-1, -1⟩ ⟨1, -1⟩
  | c08 : ForbiddenSmallSuccessor ⟨-1, -1⟩ ⟨2, 0⟩
  | c09 : ForbiddenSmallSuccessor ⟨-1, 1⟩ ⟨0, 2⟩
  | c10 : ForbiddenSmallSuccessor ⟨-1, 1⟩ ⟨1, 1⟩
  | c11 : ForbiddenSmallSuccessor ⟨-1, 1⟩ ⟨2, 0⟩
  | c12 : ForbiddenSmallSuccessor ⟨-1, 2⟩ ⟨1, 1⟩
  | c13 : ForbiddenSmallSuccessor ⟨0, -2⟩ ⟨-1, -1⟩
  | c14 : ForbiddenSmallSuccessor ⟨0, -2⟩ ⟨1, -1⟩
  | c15 : ForbiddenSmallSuccessor ⟨0, 2⟩ ⟨-1, 1⟩
  | c16 : ForbiddenSmallSuccessor ⟨0, 2⟩ ⟨1, 1⟩
  | c17 : ForbiddenSmallSuccessor ⟨1, -2⟩ ⟨-1, -1⟩
  | c18 : ForbiddenSmallSuccessor ⟨1, -1⟩ ⟨-2, 0⟩
  | c19 : ForbiddenSmallSuccessor ⟨1, -1⟩ ⟨-1, -1⟩
  | c20 : ForbiddenSmallSuccessor ⟨1, -1⟩ ⟨0, -2⟩
  | c21 : ForbiddenSmallSuccessor ⟨1, 1⟩ ⟨-2, 0⟩
  | c22 : ForbiddenSmallSuccessor ⟨1, 1⟩ ⟨-1, 1⟩
  | c23 : ForbiddenSmallSuccessor ⟨1, 1⟩ ⟨0, 2⟩
  | c24 : ForbiddenSmallSuccessor ⟨1, 2⟩ ⟨-1, 1⟩
  | c25 : ForbiddenSmallSuccessor ⟨2, -1⟩ ⟨-1, -1⟩
  | c26 : ForbiddenSmallSuccessor ⟨2, 0⟩ ⟨-1, -1⟩
  | c27 : ForbiddenSmallSuccessor ⟨2, 0⟩ ⟨-1, 1⟩
  | c28 : ForbiddenSmallSuccessor ⟨2, 1⟩ ⟨-1, 1⟩

private abbrev IsForbiddenSmallSuccessorPair := ForbiddenSmallSuccessor

private theorem successorGap_test_identity (sigma : Gaussian) :
    successorGap ⟨-2, -1⟩ ⟨1, -1⟩ (-1) sigma = normSq sigma - 1 := by
  simp [successorGap, normSq, toGaussian]
  ring1

private theorem neg_one_add_twice_lt_zero_of_lt_half
    {value : Coordinate} (upper : value < 1 / 2) :
    -1 + 2 * value < 0 := by
  have doubled := twice_lt_one_of_lt_half upper
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    doubled (-1)
  calc
    -1 + 2 * value = 2 * value + -1 := by ring1
    _ < 1 + -1 := shifted
    _ = 0 := by ring1

private theorem neg_one_sub_twice_lt_zero_of_neg_half_lt
    {value : Coordinate} (lower : -(1 / 2 : Coordinate) < value) :
    -1 - 2 * value < 0 := by
  have doubled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (show (0 : Coordinate) < 2 by decide) lower
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    doubled (-(2 * value))
  calc
    -1 - 2 * value = -1 + -(2 * value) := by ring1
    _ = 2 * (-(1 / 2 : Coordinate)) + -(2 * value) := by
      rw [show (2 : Coordinate) * (-(1 / 2)) = -1 by decide]
    _ < 2 * value + -(2 * value) := shifted
    _ = 0 := by ring1

private theorem neg_three_add_twice_lt_zero_of_lt_half
    {value : Coordinate} (upper : value < 1 / 2) :
    -3 + 2 * value < 0 := by
  have oneGap := neg_one_add_twice_lt_zero_of_lt_half upper
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    oneGap (-2)
  calc
    -3 + 2 * value = (-1 + 2 * value) + -2 := by ring1
    _ < 0 + -2 := shifted
    _ < 0 := by decide

private theorem neg_three_sub_twice_lt_zero_of_neg_half_le
    {value : Coordinate} (lower : -(1 / 2 : Coordinate) ≤ value) :
    -3 - 2 * value < 0 := by
  have doubled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    lower (show (0 : Coordinate) ≤ 2 by decide)
  have negated := RFAP.ConstructiveFraction.neg_le_neg_direct doubled
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    negated (-3)
  calc
    -3 - 2 * value = -(2 * value) + -3 := by ring1
    _ ≤ -(2 * (-(1 / 2 : Coordinate))) + -3 := shifted
    _ = -2 := by decide
    _ < 0 := by decide

/-- No actual pair of adjacent noninitial Hurwitz digits belongs to the
finite exceptional relation.  Each constructor is discharged by one exact
cleared exterior-disc calculation. -/
theorem not_forbiddenSmallSuccessor
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0) :
    ¬ ForbiddenSmallSuccessor
      (digit (next fraction nonterminal))
      (digit (next (next fraction nonterminal) nextNonterminal)) := by
  let following := next (next fraction nonterminal) nextNonterminal
  let sigma := residual following
  have sigmaSquare := RFAP.HurwitzNearest.remainder_mem following.value
  have sigmaNormLtOne : normSq sigma < 1 := by
    exact
      (RFAP.HurwitzNearest.remainder_normSq_le_half following.value).trans_lt
        (show (1 / 2 : Coordinate) < 1 by decide)
  have normGap : normSq sigma - 1 < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct sigmaNormLtOne
  have realUpperGap : -1 + 2 * sigma.re < 0 :=
    neg_one_add_twice_lt_zero_of_lt_half sigmaSquare.2.1
  have imaginaryUpperGap : -1 + 2 * sigma.im < 0 :=
    neg_one_add_twice_lt_zero_of_lt_half sigmaSquare.2.2.2
  have realUpperThreeGap : -3 + 2 * sigma.re < 0 :=
    neg_three_add_twice_lt_zero_of_lt_half sigmaSquare.2.1
  have imaginaryUpperThreeGap : -3 + 2 * sigma.im < 0 :=
    neg_three_add_twice_lt_zero_of_lt_half sigmaSquare.2.2.2
  have realLowerThreeGap : -3 - 2 * sigma.re < 0 :=
    neg_three_sub_twice_lt_zero_of_neg_half_le sigmaSquare.1
  have imaginaryLowerThreeGap : -3 - 2 * sigma.im < 0 :=
    neg_three_sub_twice_lt_zero_of_neg_half_le sigmaSquare.2.2.1
  intro forbidden
  generalize previousDigitValue : digit (next fraction nonterminal) =
    previousDigit at forbidden
  generalize followingDigitValue :
    digit (next (next fraction nonterminal) nextNonterminal) =
      followingDigit at forbidden
  cases forbidden with
  | c01 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, -1⟩ ⟨1, -1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-2, -1⟩ ⟨1, -1⟩ (-1) sigma < 0
      rw [successorGap_test_identity]
      exact normGap
  | c02 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, 0⟩ ⟨1, -1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      have strictLower := next_residual_real_lower_strict_of_one_sub_i
        (next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨-2, 0⟩ ⟨1, -1⟩ (-1) sigma < 0
      convert negative using 1 ;
        simp [successorGap, normSq, toGaussian, sigma, following] ; ring1
  | c03 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, 0⟩ ⟨1, 1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      have strictLower := next_residual_real_lower_strict_of_one_add_i
        (next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨-2, 0⟩ ⟨1, 1⟩ (-1) sigma < 0
      convert negative using 1 ;
        simp [successorGap, normSq, toGaussian, sigma, following] ; ring1
  | c04 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, 1⟩ ⟨1, 1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-2, 1⟩ ⟨1, 1⟩ (-1) sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c05 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c06 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -1⟩ ⟨0, -2⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -1⟩ ⟨0, -2⟩ (-1) sigma < 0
      convert imaginaryUpperThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c07 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -1⟩ ⟨1, -1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -1⟩ ⟨1, -1⟩ (-1) sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c08 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -1⟩ ⟨2, 0⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -1⟩ ⟨2, 0⟩ ⟨0, -1⟩ sigma < 0
      convert realLowerThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c09 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 1⟩ ⟨0, 2⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-1, 1⟩ ⟨0, 2⟩ (-1) sigma < 0
      convert imaginaryLowerThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c10 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 1⟩ ⟨1, 1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_one_add_i
        (next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨-1, 1⟩ ⟨1, 1⟩ (-1) sigma < 0
      convert negative using 1 ;
        simp [successorGap, normSq, toGaussian, sigma, following] ; ring1
  | c11 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 1⟩ ⟨2, 0⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, 1⟩ ⟨2, 0⟩ ⟨0, 1⟩ sigma < 0
      convert realLowerThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c12 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c13 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨0, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c14 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨0, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c15 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_neg_one_add_i
        (next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨0, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert negative using 1 ;
        simp [successorGap, normSq, toGaussian, sigma, following] ; ring1
  | c16 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_one_add_i
        (next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨0, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert negative using 1 ;
        simp [successorGap, normSq, toGaussian, sigma, following] ; ring1
  | c17 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c18 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -1⟩ ⟨-2, 0⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, -1⟩ ⟨-2, 0⟩ ⟨0, -1⟩ sigma < 0
      convert realUpperThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c19 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -1⟩ ⟨-1, -1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨1, -1⟩ ⟨-1, -1⟩ 1 sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c20 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -1⟩ ⟨0, -2⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨1, -1⟩ ⟨0, -2⟩ 1 sigma < 0
      convert imaginaryUpperThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c21 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 1⟩ ⟨-2, 0⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, 1⟩ ⟨-2, 0⟩ ⟨0, 1⟩ sigma < 0
      convert realUpperThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c22 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 1⟩ ⟨-1, 1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_neg_one_add_i
        (next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨1, 1⟩ ⟨-1, 1⟩ 1 sigma < 0
      convert negative using 1 ;
        simp [successorGap, normSq, toGaussian, sigma, following] ; ring1
  | c23 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 1⟩ ⟨0, 2⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨1, 1⟩ ⟨0, 2⟩ 1 sigma < 0
      convert imaginaryLowerThreeGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c24 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c25 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, -1⟩ ⟨-1, -1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, -1⟩ ⟨-1, -1⟩ 1 sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c26 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, 0⟩ ⟨-1, -1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, 0⟩ ⟨-1, -1⟩ 1 sigma < 0
      convert realUpperGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c27 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, 0⟩ ⟨-1, 1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, 0⟩ ⟨-1, 1⟩ 1 sigma < 0
      convert realUpperGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1
  | c28 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, 1⟩ ⟨-1, 1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, 1⟩ ⟨-1, 1⟩ 1 sigma < 0
      convert normGap using 1 ;
        simp [successorGap, normSq, toGaussian] ; ring1

/-- A displayed binary Hermitian form.  The four scalar coefficients are
rational, so transformations of the form are finite ring calculations. -/
def finiteHermitianForm (constant radial realCross imaginaryCross : Coordinate)
    (value : Gaussian) : Coordinate :=
  constant + radial * normSq value +
    2 * (realCross * value.re + imaginaryCross * value.im)

/-- A rational certificate that a binary Hermitian form is nonnegative on
the closed unit disc.  The identity used here is a completed-square identity,
with `slack` supplied explicitly rather than selected by an existence proof. -/
theorem finiteHermitianForm_nonnegative_of_certificate
    (constant radial realCross imaginaryCross : Coordinate)
    (value : Gaussian) (slack : Coordinate)
    (valueInside : normSq value ≤ 1)
    (slackNonnegative : 0 ≤ slack)
    (scalePositive : 0 < radial + slack)
    (determinantGap :
      0 ≤ (constant - slack) * (radial + slack) -
        (realCross ^ 2 + imaginaryCross ^ 2)) :
    0 ≤ finiteHermitianForm constant radial realCross imaginaryCross value := by
  let scale := radial + slack
  have scaleNonnegative : 0 ≤ scale := scalePositive.le
  have discGap : 0 ≤ 1 - normSq value :=
    RFAP.ConstructiveFraction.sub_nonneg_direct valueInside
  have scaledDiscGap :
      0 ≤ scale * slack * (1 - normSq value) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        scaleNonnegative slackNonnegative) discGap
  have realSquare :
      0 ≤ (scale * value.re + realCross) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have imaginarySquare :
      0 ≤ (scale * value.im + imaginaryCross) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have certificateNonnegative :
      0 ≤
        (scale * value.re + realCross) ^ 2 +
          (scale * value.im + imaginaryCross) ^ 2 +
          scale * slack * (1 - normSq value) +
          ((constant - slack) * scale -
            (realCross ^ 2 + imaginaryCross ^ 2)) :=
    add_nonneg
      (add_nonneg (add_nonneg realSquare imaginarySquare) scaledDiscGap)
      determinantGap
  have productNonnegative :
      0 ≤ scale *
        finiteHermitianForm constant radial realCross imaginaryCross value := by
    calc
      0 ≤
          (scale * value.re + realCross) ^ 2 +
            (scale * value.im + imaginaryCross) ^ 2 +
            scale * slack * (1 - normSq value) +
            ((constant - slack) * scale -
              (realCross ^ 2 + imaginaryCross ^ 2)) :=
        certificateNonnegative
      _ = scale *
          finiteHermitianForm constant radial realCross imaginaryCross value := by
        dsimp only [scale, finiteHermitianForm, normSq]
        ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := scale) _ scalePositive
  calc
    0 * scale = 0 := by ring1
    _ ≤ scale *
        finiteHermitianForm constant radial realCross imaginaryCross value :=
      productNonnegative
    _ = finiteHermitianForm constant radial realCross imaginaryCross value *
        scale := by ring1

/-- Clearing one reciprocal step transforms the displayed Hermitian form by
an exact coefficient calculation. -/
theorem finiteHermitianForm_inverse_add_mul_normSq
    (constant radial realCross imaginaryCross : Coordinate)
    (coefficient : GaussianInt) (value : Gaussian)
    (sumNonzero : toGaussian coefficient + value ≠ 0) :
    finiteHermitianForm constant radial realCross imaginaryCross
          ((toGaussian coefficient + value)⁻¹) *
        normSq (toGaussian coefficient + value) =
      finiteHermitianForm
        (constant * (normNat coefficient : Coordinate) + radial +
          2 *
            (realCross * (coefficient.re : Coordinate) -
              imaginaryCross * (coefficient.im : Coordinate)))
        constant
        (constant * (coefficient.re : Coordinate) + realCross)
        (constant * (coefficient.im : Coordinate) - imaginaryCross)
        value := by
  let sum := toGaussian coefficient + value
  have normNonzero : normSq sum ≠ 0 := by
    intro normZero
    exact sumNonzero (normSq_eq_zero.mp normZero)
  have realCancel : sum⁻¹.re * normSq sum = sum.re := by
    rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq]
    change (sum.re / normSq sum) * normSq sum = sum.re
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ normNonzero
  have imaginaryCancel : sum⁻¹.im * normSq sum = -sum.im := by
    rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq]
    change ((-sum.im) / normSq sum) * normSq sum = -sum.im
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ normNonzero
  have inverseNormCancel : normSq sum⁻¹ * normSq sum = 1 := by
    rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq, normSq_inv sum sumNonzero]
    calc
      (normSq sum)⁻¹ * normSq sum =
          normSq sum * (normSq sum)⁻¹ :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = 1 :=
        RFAP.ConstructiveFraction.mul_inv_cancel _ normNonzero
  calc
    finiteHermitianForm constant radial realCross imaginaryCross sum⁻¹ *
          normSq sum =
        constant * normSq sum + radial * (normSq sum⁻¹ * normSq sum) +
          2 *
            (realCross * (sum⁻¹.re * normSq sum) +
              imaginaryCross * (sum⁻¹.im * normSq sum)) := by
      dsimp only [finiteHermitianForm]
      ring1
    _ = constant * normSq sum + radial +
          2 * (realCross * sum.re - imaginaryCross * sum.im) := by
      rw [inverseNormCancel, realCancel, imaginaryCancel]
      ring1
    _ = finiteHermitianForm
        (constant * (normNat coefficient : Coordinate) + radial +
          2 *
            (realCross * (coefficient.re : Coordinate) -
              imaginaryCross * (coefficient.im : Coordinate)))
        constant
        (constant * (coefficient.re : Coordinate) + realCross)
        (constant * (coefficient.im : Coordinate) - imaginaryCross)
        value := by
      dsimp only [sum, finiteHermitianForm]
      rw [← normSq_toGaussian coefficient]
      simp only [normSq,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian]
      ring1

/-- Integral coefficient data for the finite Hermitian forms occurring in
the Lakein recursion. -/
structure IntegralHermitianForm where
  constant : Int
  radial : Int
  realCross : Int
  imaginaryCross : Int
deriving DecidableEq

def IntegralHermitianForm.evaluate (form : IntegralHermitianForm)
    (value : Gaussian) : Coordinate :=
  finiteHermitianForm (form.constant : Coordinate)
    (form.radial : Coordinate) (form.realCross : Coordinate)
    (form.imaginaryCross : Coordinate) value

/-- Exact integral pullback of a Hermitian form through `z ↦ (a+z)⁻¹`. -/
def IntegralHermitianForm.pullback (form : IntegralHermitianForm)
    (coefficient : GaussianInt) : IntegralHermitianForm :=
  { constant :=
      form.constant * normInt coefficient + form.radial +
        2 * (form.realCross * coefficient.re -
          form.imaginaryCross * coefficient.im)
    radial := form.constant
    realCross := form.constant * coefficient.re + form.realCross
    imaginaryCross := form.constant * coefficient.im - form.imaginaryCross }

def IntegralHermitianForm.determinant (form : IntegralHermitianForm) : Int :=
  form.constant * form.radial -
    (form.realCross * form.realCross +
      form.imaginaryCross * form.imaginaryCross)

theorem IntegralHermitianForm.pullback_determinant
    (form : IntegralHermitianForm) (coefficient : GaussianInt) :
    (form.pullback coefficient).determinant = form.determinant := by
  dsimp only [IntegralHermitianForm.pullback,
    IntegralHermitianForm.determinant, normInt]
  ring1

private theorem integral_square_nonnegative (value : Int) :
    0 ≤ value * value := by
  by_cases nonnegative : 0 ≤ value
  · exact Int.mul_nonneg nonnegative nonnegative
  · have nonpositive : value ≤ 0 :=
      Int.le_of_lt (Int.lt_of_not_ge nonnegative)
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

private theorem false_of_decide_false {proposition : Prop}
    [Decidable proposition] (holds : proposition)
    (fails : decide proposition = false) : False := by
  rw [decide_eq_true holds] at fails
  exact Bool.noConfusion fails

theorem IntegralHermitianForm.pullback_constant_lower
    (form : IntegralHermitianForm) (coefficient : GaussianInt) :
    (form.constant - 1) * normInt coefficient + form.radial -
        (form.realCross * form.realCross +
          form.imaginaryCross * form.imaginaryCross) ≤
      (form.pullback coefficient).constant := by
  have realSquare := integral_square_nonnegative
    (coefficient.re + form.realCross)
  have imaginarySquare := integral_square_nonnegative
    (coefficient.im - form.imaginaryCross)
  have sumNonnegative :
      0 ≤ (coefficient.re + form.realCross) *
          (coefficient.re + form.realCross) +
        (coefficient.im - form.imaginaryCross) *
          (coefficient.im - form.imaginaryCross) :=
    Int.add_nonneg realSquare imaginarySquare
  have differenceIdentity :
      (form.pullback coefficient).constant -
          ((form.constant - 1) * normInt coefficient + form.radial -
            (form.realCross * form.realCross +
              form.imaginaryCross * form.imaginaryCross)) =
        (coefficient.re + form.realCross) *
            (coefficient.re + form.realCross) +
          (coefficient.im - form.imaginaryCross) *
            (coefficient.im - form.imaginaryCross) := by
    dsimp only [IntegralHermitianForm.pullback, normInt]
    ring1
  rw [← differenceIdentity] at sumNonnegative
  have shifted := Int.add_le_add_right sumNonnegative
    ((form.constant - 1) * normInt coefficient + form.radial -
      (form.realCross * form.realCross +
        form.imaginaryCross * form.imaginaryCross))
  calc
    (form.constant - 1) * normInt coefficient + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross) =
        0 + ((form.constant - 1) * normInt coefficient + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross)) := by ring1
    _ ≤ ((form.pullback coefficient).constant -
          ((form.constant - 1) * normInt coefficient + form.radial -
            (form.realCross * form.realCross +
              form.imaginaryCross * form.imaginaryCross))) +
        ((form.constant - 1) * normInt coefficient + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross)) := shifted
    _ = (form.pullback coefficient).constant := by ring1

theorem IntegralHermitianForm.evaluate_pullback_mul_normSq
    (form : IntegralHermitianForm) (coefficient : GaussianInt)
    (value : Gaussian) (sumNonzero : toGaussian coefficient + value ≠ 0) :
    form.evaluate ((toGaussian coefficient + value)⁻¹) *
        normSq (toGaussian coefficient + value) =
      (form.pullback coefficient).evaluate value := by
  have transformed := finiteHermitianForm_inverse_add_mul_normSq
    (form.constant : Coordinate) (form.radial : Coordinate)
    (form.realCross : Coordinate) (form.imaginaryCross : Coordinate)
    coefficient value sumNonzero
  simpa only [IntegralHermitianForm.evaluate,
    IntegralHermitianForm.pullback, normInt_eq_natCast_normNat,
    Int.cast_add, Int.cast_sub, QuotientFreeRing.intCast_mul, Int.cast_ofNat,
    Int.cast_natCast] using transformed

/-- An explicit slack-one certificate for an integral Hermitian form. -/
theorem IntegralHermitianForm.evaluate_nonnegative_of_slack_one
    (form : IntegralHermitianForm) (value : Gaussian)
    (valueInside : normSq value ≤ 1)
    (scalePositive : 0 < (form.radial : Coordinate) + 1)
    (determinantGap :
      0 ≤ ((form.constant : Coordinate) - 1) *
          ((form.radial : Coordinate) + 1) -
        ((form.realCross : Coordinate) ^ 2 +
          (form.imaginaryCross : Coordinate) ^ 2)) :
    0 ≤ form.evaluate value := by
  exact finiteHermitianForm_nonnegative_of_certificate
    (form.constant : Coordinate) (form.radial : Coordinate)
    (form.realCross : Coordinate) (form.imaginaryCross : Coordinate)
    value 1 valueInside (by decide) scalePositive determinantGap

/-- The eight cross terms of the quadrance-five/diagonal denominator
comparison. -/
inductive IsLakeinRootCross : Int → Int → Prop
  | negativeThreeNegativeOne : IsLakeinRootCross (-3) (-1)
  | negativeThreePositiveOne : IsLakeinRootCross (-3) 1
  | negativeOneNegativeThree : IsLakeinRootCross (-1) (-3)
  | negativeOnePositiveThree : IsLakeinRootCross (-1) 3
  | positiveOneNegativeThree : IsLakeinRootCross 1 (-3)
  | positiveOnePositiveThree : IsLakeinRootCross 1 3
  | positiveThreeNegativeOne : IsLakeinRootCross 3 (-1)
  | positiveThreePositiveOne : IsLakeinRootCross 3 1

def lakeinRootForm (realCross imaginaryCross : Int) :
    IntegralHermitianForm :=
  ⟨4, 2, realCross, imaginaryCross⟩

def LakeinRootFormsNonnegative (value : Gaussian) : Prop :=
  ∀ realCross imaginaryCross,
    IsLakeinRootCross realCross imaginaryCross →
      0 ≤ (lakeinRootForm realCross imaginaryCross).evaluate value

private theorem lakeinRootForm_determinant
    {realCross imaginaryCross : Int}
    (root : IsLakeinRootCross realCross imaginaryCross) :
    (lakeinRootForm realCross imaginaryCross).determinant = -2 := by
  cases root <;> decide

private theorem evaluate_root_plus_four_unit_square_nonnegative
    (value : Gaussian) {realCross imaginaryCross : Int}
    (rootNonnegative :
      0 ≤ (lakeinRootForm realCross imaginaryCross).evaluate value)
    (unit : GaussianInt) (unitProperty : IsGaussianUnit unit) :
    0 ≤
      (⟨8, 6, realCross + 4 * unit.re,
          imaginaryCross + 4 * unit.im⟩ : IntegralHermitianForm).evaluate
        value := by
  have squareNonnegative :
      0 ≤ 4 * normSq (value + toGaussian unit) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (show (0 : Coordinate) ≤ 4 by decide) (normSq_nonneg _)
  have sumNonnegative := add_nonneg rootNonnegative squareNonnegative
  calc
    0 ≤
        (lakeinRootForm realCross imaginaryCross).evaluate value +
          4 * normSq (value + toGaussian unit) := sumNonnegative
    _ = (⟨8, 6, realCross + 4 * unit.re,
          imaginaryCross + 4 * unit.im⟩ : IntegralHermitianForm).evaluate
        value := by
      rcases unitProperty with rfl | rfl | rfl | rfl
      all_goals simp [IntegralHermitianForm.evaluate, lakeinRootForm,
        finiteHermitianForm, normSq, toGaussian]
      all_goals ring1

theorem IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
    (form : IntegralHermitianForm) (coefficient : GaussianInt)
    (value : Gaussian) (valueInside : normSq value ≤ 1)
    (scalePositive : 0 < (form.constant : Coordinate) + 1)
    (determinantValue : form.determinant = -2)
    (constantGap :
      form.constant + 3 ≤ (form.pullback coefficient).constant) :
    0 ≤ (form.pullback coefficient).evaluate value := by
  let pulled := form.pullback coefficient
  have pulledDeterminant : pulled.determinant = -2 := by
    dsimp only [pulled]
    rw [IntegralHermitianForm.pullback_determinant, determinantValue]
  have castGap :
      (form.constant : Coordinate) + 3 ≤
        (pulled.constant : Coordinate) := by
    have cast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
        (form.constant + 3) pulled.constant).2 constantGap
    simpa only [Int.cast_add, Int.cast_ofNat] using cast
  have differenceNonnegative :
      0 ≤ (pulled.constant : Coordinate) -
        (form.constant : Coordinate) - 3 := by
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      castGap (-(form.constant : Coordinate) - 3)
    calc
      0 = (form.constant : Coordinate) + 3 +
          (-(form.constant : Coordinate) - 3) := by ring1
      _ ≤ (pulled.constant : Coordinate) +
          (-(form.constant : Coordinate) - 3) := shifted
      _ = (pulled.constant : Coordinate) -
          (form.constant : Coordinate) - 3 := by ring1
  apply IntegralHermitianForm.evaluate_nonnegative_of_slack_one
    pulled value valueInside
  · change 0 < (form.constant : Coordinate) + 1
    exact scalePositive
  · have determinantCast := congrArg
      (fun value : Int => (value : Coordinate)) pulledDeterminant
    simp only [Int.cast_neg, Int.cast_ofNat] at determinantCast
    calc
      0 ≤ (pulled.constant : Coordinate) -
          (form.constant : Coordinate) - 3 := differenceNonnegative
      _ = ((pulled.constant : Coordinate) - 1) *
            ((pulled.radial : Coordinate) + 1) -
          ((pulled.realCross : Coordinate) ^ 2 +
            (pulled.imaginaryCross : Coordinate) ^ 2) := by
        have radialIdentity : pulled.radial = form.constant := rfl
        rw [radialIdentity]
        have determinantExpanded :
            (pulled.constant : Coordinate) *
                  (form.constant : Coordinate) -
                ((pulled.realCross : Coordinate) *
                    (pulled.realCross : Coordinate) +
                    (pulled.imaginaryCross : Coordinate) *
                    (pulled.imaginaryCross : Coordinate)) = -2 := by
          simp only [IntegralHermitianForm.determinant, Int.cast_sub,
            QuotientFreeRing.intCast_mul, Int.cast_add] at determinantCast
          rw [radialIdentity] at determinantCast
          exact determinantCast
        rw [pow_two, pow_two]
        calc
          (pulled.constant : Coordinate) -
                (form.constant : Coordinate) - 3 =
              ((pulled.constant : Coordinate) *
                  (form.constant : Coordinate) -
                ((pulled.realCross : Coordinate) *
                    (pulled.realCross : Coordinate) +
                  (pulled.imaginaryCross : Coordinate) *
                    (pulled.imaginaryCross : Coordinate))) +
                (pulled.constant : Coordinate) -
                (form.constant : Coordinate) - 1 := by
            rw [determinantExpanded]
            ring1
          _ = ((pulled.constant : Coordinate) - 1) *
                ((form.constant : Coordinate) + 1) -
              ((pulled.realCross : Coordinate) *
                  (pulled.realCross : Coordinate) +
                (pulled.imaginaryCross : Coordinate) *
                  (pulled.imaginaryCross : Coordinate)) := by ring1

/-- The twenty-four first-step forms not settled by the slack-one
certificate.  The following digit is retained because it is needed by the
second-step succession check. -/
inductive FirstExceptionalHermitian :
    IntegralHermitianForm → GaussianInt → Prop
  | c01 : FirstExceptionalHermitian ⟨6, 4, 1, 5⟩ ⟨1, 1⟩
  | c02 : FirstExceptionalHermitian ⟨2, 4, 1, -3⟩ ⟨1, -1⟩
  | c03 : FirstExceptionalHermitian ⟨6, 4, 5, 1⟩ ⟨2, 0⟩
  | c04 : FirstExceptionalHermitian ⟨2, 4, 1, 3⟩ ⟨1, 1⟩
  | c05 : FirstExceptionalHermitian ⟨6, 4, 1, -5⟩ ⟨1, -1⟩
  | c06 : FirstExceptionalHermitian ⟨6, 4, 5, -1⟩ ⟨2, 0⟩
  | c07 : FirstExceptionalHermitian ⟨2, 4, 3, -1⟩ ⟨1, -1⟩
  | c08 : FirstExceptionalHermitian ⟨6, 4, -5, -1⟩ ⟨-1, -1⟩
  | c09 : FirstExceptionalHermitian ⟨6, 4, -1, -5⟩ ⟨0, -2⟩
  | c10 : FirstExceptionalHermitian ⟨2, 4, 3, 1⟩ ⟨1, 1⟩
  | c11 : FirstExceptionalHermitian ⟨6, 4, -5, 1⟩ ⟨-1, 1⟩
  | c12 : FirstExceptionalHermitian ⟨6, 4, -1, 5⟩ ⟨0, 2⟩
  | c13 : FirstExceptionalHermitian ⟨6, 4, 5, -1⟩ ⟨1, -1⟩
  | c14 : FirstExceptionalHermitian ⟨2, 4, -3, -1⟩ ⟨-1, -1⟩
  | c15 : FirstExceptionalHermitian ⟨6, 4, 1, -5⟩ ⟨0, -2⟩
  | c16 : FirstExceptionalHermitian ⟨6, 4, 5, 1⟩ ⟨1, 1⟩
  | c17 : FirstExceptionalHermitian ⟨2, 4, -3, 1⟩ ⟨-1, 1⟩
  | c18 : FirstExceptionalHermitian ⟨6, 4, 1, 5⟩ ⟨0, 2⟩
  | c19 : FirstExceptionalHermitian ⟨6, 4, -1, 5⟩ ⟨-1, 1⟩
  | c20 : FirstExceptionalHermitian ⟨2, 4, -1, -3⟩ ⟨-1, -1⟩
  | c21 : FirstExceptionalHermitian ⟨6, 4, -5, 1⟩ ⟨-2, 0⟩
  | c22 : FirstExceptionalHermitian ⟨2, 4, -1, 3⟩ ⟨-1, 1⟩
  | c23 : FirstExceptionalHermitian ⟨6, 4, -1, -5⟩ ⟨-1, -1⟩
  | c24 : FirstExceptionalHermitian ⟨6, 4, -5, -1⟩ ⟨-2, 0⟩

private theorem root_pullback_constant_gap_or_exceptional
    {realCross imaginaryCross : Int}
    (root : IsLakeinRootCross realCross imaginaryCross)
    (coefficient : GaussianInt) (coefficientNorm : 2 ≤ normNat coefficient) :
    7 ≤
        ((lakeinRootForm realCross imaginaryCross).pullback coefficient).constant ∨
      FirstExceptionalHermitian
        ((lakeinRootForm realCross imaginaryCross).pullback coefficient)
        coefficient := by
  by_cases large : 5 ≤ normNat coefficient
  · left
    have normIntLarge : (5 : Int) ≤ normInt coefficient := by
      rw [normInt_eq_natCast_normNat]
      exact Int.ofNat_le.mpr large
    have scaledLarge : (3 : Int) * 5 ≤ 3 * normInt coefficient :=
      Int.mul_le_mul_of_nonneg_left normIntLarge (by decide)
    have constantGap : (7 : Int) ≤ 3 * normInt coefficient - 8 := by
      calc
        (7 : Int) = 3 * 5 - 8 := by decide
        _ ≤ 3 * normInt coefficient - 8 := by
          rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg]
          exact Int.add_le_add_right scaledLarge (-8)
    have rootSquare :
        realCross * realCross + imaginaryCross * imaginaryCross = 10 := by
      cases root <;> decide
    have lower := IntegralHermitianForm.pullback_constant_lower
      (lakeinRootForm realCross imaginaryCross) coefficient
    calc
      (7 : Int) ≤ 3 * normInt coefficient - 8 := constantGap
      _ =
          ((lakeinRootForm realCross imaginaryCross).constant - 1) *
              normInt coefficient +
            (lakeinRootForm realCross imaginaryCross).radial -
              ((lakeinRootForm realCross imaginaryCross).realCross *
                  (lakeinRootForm realCross imaginaryCross).realCross +
                (lakeinRootForm realCross imaginaryCross).imaginaryCross *
                  (lakeinRootForm realCross imaginaryCross).imaginaryCross) := by
            dsimp only [lakeinRootForm]
            rw [rootSquare]
            ring1
      _ ≤ ((lakeinRootForm realCross imaginaryCross).pullback coefficient).constant :=
        lower
  · have small : normNat coefficient < 5 := Nat.lt_of_not_ge large
    have cases := normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six
      coefficient (small.trans (by decide))
    rcases cases with zero | one | two | four | five
    · rw [zero] at coefficientNorm
      exact False.elim ((by decide : ¬2 ≤ 0) coefficientNorm)
    · rw [one] at coefficientNorm
      exact False.elim ((by decide : ¬2 ≤ 1) coefficientNorm)
    · have concrete := isDiagonal_of_normNat_eq_two two
      rcases concrete with rfl | rfl | rfl | rfl
      all_goals cases root
      all_goals first
        | exact Or.inl (by decide)
        | exact Or.inr FirstExceptionalHermitian.c01
        | exact Or.inr FirstExceptionalHermitian.c02
        | exact Or.inr FirstExceptionalHermitian.c04
        | exact Or.inr FirstExceptionalHermitian.c05
        | exact Or.inr FirstExceptionalHermitian.c07
        | exact Or.inr FirstExceptionalHermitian.c08
        | exact Or.inr FirstExceptionalHermitian.c10
        | exact Or.inr FirstExceptionalHermitian.c11
        | exact Or.inr FirstExceptionalHermitian.c13
        | exact Or.inr FirstExceptionalHermitian.c14
        | exact Or.inr FirstExceptionalHermitian.c16
        | exact Or.inr FirstExceptionalHermitian.c17
        | exact Or.inr FirstExceptionalHermitian.c19
        | exact Or.inr FirstExceptionalHermitian.c20
        | exact Or.inr FirstExceptionalHermitian.c22
        | exact Or.inr FirstExceptionalHermitian.c23
    · have concrete := axisDouble_cases_of_normNat_eq_four four
      rcases concrete with rfl | rfl | rfl | rfl
      all_goals cases root
      all_goals first
        | exact Or.inl (by decide)
        | exact Or.inr FirstExceptionalHermitian.c03
        | exact Or.inr FirstExceptionalHermitian.c06
        | exact Or.inr FirstExceptionalHermitian.c09
        | exact Or.inr FirstExceptionalHermitian.c12
        | exact Or.inr FirstExceptionalHermitian.c15
        | exact Or.inr FirstExceptionalHermitian.c18
        | exact Or.inr FirstExceptionalHermitian.c21
        | exact Or.inr FirstExceptionalHermitian.c24
    · rw [five] at small
      exact False.elim ((Nat.lt_irrefl 5) small)

private theorem coordinate_cases_of_square_lt_sixteen {value : Int}
    (small : value * value < 16) :
    value = -3 ∨ value = -2 ∨ value = -1 ∨ value = 0 ∨
      value = 1 ∨ value = 2 ∨ value = 3 := by
  have lower : -(4 : Int) < value := by
    apply Int.lt_of_not_ge
    intro valueAtMost
    have fourLeNegative : (4 : Int) ≤ -value := by
      have negated := Int.neg_le_neg valueAtMost
      change (4 : Int) ≤ -value at negated
      exact negated
    have squareAtLeastSixteen : (16 : Int) ≤ value * value := by
      calc
        (16 : Int) = 4 * 4 := rfl
        _ ≤ (-value) * (-value) :=
          Int.mul_self_le_mul_self (by decide) fourLeNegative
        _ = value * value := by ring1
    exact (not_lt_of_ge squareAtLeastSixteen small)
  have upper : value < 4 := by
    apply Int.lt_of_not_ge
    intro fourLeValue
    have squareAtLeastSixteen : (16 : Int) ≤ value * value := by
      calc
        (16 : Int) = 4 * 4 := rfl
        _ ≤ value * value :=
          Int.mul_self_le_mul_self (by decide) fourLeValue
    exact (not_lt_of_ge squareAtLeastSixteen small)
  have lowerLe : (-3 : Int) ≤ value := by
    change (-(4 : Int) + 1) ≤ value
    exact Int.add_one_le_iff.mpr lower
  have upperLe : value ≤ (3 : Int) := by
    change value ≤ (4 : Int) - 1
    exact Int.le_sub_one_iff.mpr upper
  by_cases negThree : value = -3
  · exact Or.inl negThree
  have negTwoLe : (-2 : Int) ≤ value := by
    change (-3 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne lowerLe (Ne.symm negThree))
  by_cases negTwo : value = -2
  · exact Or.inr (Or.inl negTwo)
  have negOneLe : (-1 : Int) ≤ value := by
    change (-2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne negTwoLe (Ne.symm negTwo))
  by_cases negOne : value = -1
  · exact Or.inr (Or.inr (Or.inl negOne))
  have zeroLe : (0 : Int) ≤ value := by
    change (-1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne negOneLe (Ne.symm negOne))
  by_cases zero : value = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inl zero)))
  have oneLe : (1 : Int) ≤ value := by
    change (0 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne zeroLe (Ne.symm zero))
  by_cases one : value = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl one))))
  have twoLe : (2 : Int) ≤ value := by
    change (1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne oneLe (Ne.symm one))
  by_cases two : value = 2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl two)))))
  have threeLe : (3 : Int) ≤ value := by
    change (2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne twoLe (Ne.symm two))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Int.le_antisymm upperLe threeLe))))))

private inductive IsSmallPreviousDigit : GaussianInt → Prop
  | c01 : IsSmallPreviousDigit ⟨-3, -1⟩
  | c02 : IsSmallPreviousDigit ⟨-3, 0⟩
  | c03 : IsSmallPreviousDigit ⟨-3, 1⟩
  | c04 : IsSmallPreviousDigit ⟨-2, -2⟩
  | c05 : IsSmallPreviousDigit ⟨-2, -1⟩
  | c06 : IsSmallPreviousDigit ⟨-2, 0⟩
  | c07 : IsSmallPreviousDigit ⟨-2, 1⟩
  | c08 : IsSmallPreviousDigit ⟨-2, 2⟩
  | c09 : IsSmallPreviousDigit ⟨-1, -3⟩
  | c10 : IsSmallPreviousDigit ⟨-1, -2⟩
  | c11 : IsSmallPreviousDigit ⟨-1, -1⟩
  | c12 : IsSmallPreviousDigit ⟨-1, 1⟩
  | c13 : IsSmallPreviousDigit ⟨-1, 2⟩
  | c14 : IsSmallPreviousDigit ⟨-1, 3⟩
  | c15 : IsSmallPreviousDigit ⟨0, -3⟩
  | c16 : IsSmallPreviousDigit ⟨0, -2⟩
  | c17 : IsSmallPreviousDigit ⟨0, 2⟩
  | c18 : IsSmallPreviousDigit ⟨0, 3⟩
  | c19 : IsSmallPreviousDigit ⟨1, -3⟩
  | c20 : IsSmallPreviousDigit ⟨1, -2⟩
  | c21 : IsSmallPreviousDigit ⟨1, -1⟩
  | c22 : IsSmallPreviousDigit ⟨1, 1⟩
  | c23 : IsSmallPreviousDigit ⟨1, 2⟩
  | c24 : IsSmallPreviousDigit ⟨1, 3⟩
  | c25 : IsSmallPreviousDigit ⟨2, -2⟩
  | c26 : IsSmallPreviousDigit ⟨2, -1⟩
  | c27 : IsSmallPreviousDigit ⟨2, 0⟩
  | c28 : IsSmallPreviousDigit ⟨2, 1⟩
  | c29 : IsSmallPreviousDigit ⟨2, 2⟩
  | c30 : IsSmallPreviousDigit ⟨3, -1⟩
  | c31 : IsSmallPreviousDigit ⟨3, 0⟩
  | c32 : IsSmallPreviousDigit ⟨3, 1⟩

private theorem isSmallPreviousDigit_of_norm_bounds
    (digit : GaussianInt) (twoLe : 2 ≤ normNat digit)
    (lessThanEleven : normNat digit < 11) :
    IsSmallPreviousDigit digit := by
  have normIntTwoLe : (2 : Int) ≤ normInt digit := by
    rw [normInt_eq_natCast_normNat]
    exact Int.ofNat_le.mpr twoLe
  have normIntSmall : normInt digit < 11 := by
    rw [normInt_eq_natCast_normNat]
    exact Int.ofNat_lt.mpr lessThanEleven
  have realSmall : digit.re * digit.re < 16 := by
    have imaginaryNonnegative := integral_square_nonnegative digit.im
    have realLeNorm : digit.re * digit.re ≤ normInt digit := by
      have shifted := Int.add_le_add_left imaginaryNonnegative
        (digit.re * digit.re)
      simpa only [normInt, Int.add_zero] using shifted
    exact realLeNorm.trans_lt (normIntSmall.trans (by decide))
  have imaginarySmall : digit.im * digit.im < 16 := by
    have realNonnegative := integral_square_nonnegative digit.re
    have imaginaryLeNorm : digit.im * digit.im ≤ normInt digit := by
      have shifted := Int.add_le_add_right realNonnegative
        (digit.im * digit.im)
      simpa only [normInt, Int.zero_add] using shifted
    exact imaginaryLeNorm.trans_lt (normIntSmall.trans (by decide))
  rcases digit with ⟨real, imaginary⟩
  change real * real < 16 at realSmall
  change imaginary * imaginary < 16 at imaginarySmall
  rcases coordinate_cases_of_square_lt_sixteen realSmall with
      realNegativeThree | realNegativeTwo | realNegativeOne | realZero |
        realPositiveOne | realPositiveTwo | realPositiveThree <;>
    rcases coordinate_cases_of_square_lt_sixteen imaginarySmall with
      imaginaryNegativeThree | imaginaryNegativeTwo | imaginaryNegativeOne |
        imaginaryZero | imaginaryPositiveOne | imaginaryPositiveTwo |
        imaginaryPositiveThree
  all_goals subst real; subst imaginary
  all_goals dsimp only [normInt] at normIntTwoLe normIntSmall
  all_goals first
    | exact False.elim
        (false_of_decide_false normIntTwoLe (by decide))
    | exact False.elim
        (false_of_decide_false normIntSmall (by decide))
    | constructor

private theorem FirstExceptionalHermitian.pullback_nonnegative_of_large
    {form : IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt) (large : 11 ≤ normNat previousDigit)
    (value : Gaussian) (valueInside : normSq value ≤ 1) :
    0 ≤ (form.pullback previousDigit).evaluate value := by
  have normIntLarge : (11 : Int) ≤ normInt previousDigit := by
    rw [normInt_eq_natCast_normNat]
    exact Int.ofNat_le.mpr large
  have lower := IntegralHermitianForm.pullback_constant_lower
    form previousDigit
  have scaledLarge : (5 : Int) * 11 ≤ 5 * normInt previousDigit :=
    Int.mul_le_mul_of_nonneg_left normIntLarge (by decide)
  have shiftedScaledLarge := Int.add_le_add_right scaledLarge (-22)
  have gapForSix : (9 : Int) ≤ 5 * normInt previousDigit - 22 := by
    calc
      (9 : Int) ≤ 5 * 11 - 22 := by decide
      _ ≤ 5 * normInt previousDigit - 22 := by
        rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg]
        exact shiftedScaledLarge
  have shiftedLarge := Int.add_le_add_right normIntLarge (-6)
  have gapForTwo : (5 : Int) ≤ normInt previousDigit - 6 := by
    calc
      (5 : Int) = 11 - 6 := by decide
      _ ≤ normInt previousDigit - 6 := by
        rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg]
        exact shiftedLarge
  have gapToLower :
      form.constant + 3 ≤
        (form.constant - 1) * normInt previousDigit + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross) := by
    cases exceptional <;> dsimp only
    all_goals first
      | convert gapForSix using 1 <;> ring1
      | convert gapForTwo using 1 <;> ring1
  have constantGap :
      form.constant + 3 ≤ (form.pullback previousDigit).constant := by
    exact gapToLower.trans lower
  have scalePositive : 0 < (form.constant : Coordinate) + 1 := by
    cases exceptional <;> decide
  have determinantValue : form.determinant = -2 := by
    cases exceptional <;> decide
  exact IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
    form previousDigit value valueInside scalePositive determinantValue
      constantGap

private inductive IsLakeinRootForm : IntegralHermitianForm → Prop
  | c01 : IsLakeinRootForm (lakeinRootForm (-3) (-1))
  | c02 : IsLakeinRootForm (lakeinRootForm (-3) 1)
  | c03 : IsLakeinRootForm (lakeinRootForm (-1) (-3))
  | c04 : IsLakeinRootForm (lakeinRootForm (-1) 3)
  | c05 : IsLakeinRootForm (lakeinRootForm 1 (-3))
  | c06 : IsLakeinRootForm (lakeinRootForm 1 3)
  | c07 : IsLakeinRootForm (lakeinRootForm 3 (-1))
  | c08 : IsLakeinRootForm (lakeinRootForm 3 1)

private inductive IsLakeinAugmentedRootForm :
    IntegralHermitianForm → Prop
  | c01 : IsLakeinAugmentedRootForm ⟨8, 6, 7, 1⟩
  | c02 : IsLakeinAugmentedRootForm ⟨8, 6, 7, -1⟩
  | c03 : IsLakeinAugmentedRootForm ⟨8, 6, -7, 1⟩
  | c04 : IsLakeinAugmentedRootForm ⟨8, 6, -7, -1⟩
  | c05 : IsLakeinAugmentedRootForm ⟨8, 6, 1, 7⟩
  | c06 : IsLakeinAugmentedRootForm ⟨8, 6, -1, 7⟩
  | c07 : IsLakeinAugmentedRootForm ⟨8, 6, 1, -7⟩
  | c08 : IsLakeinAugmentedRootForm ⟨8, 6, -1, -7⟩

private def HasLakeinSlackOneCertificate
    (form : IntegralHermitianForm) : Prop :=
  0 < form.radial + 1 ∧
    0 ≤ (form.constant - 1) * (form.radial + 1) -
      (form.realCross * form.realCross +
        form.imaginaryCross * form.imaginaryCross)

private instance hasLakeinSlackOneCertificateDecidable
    (form : IntegralHermitianForm) :
    Decidable (HasLakeinSlackOneCertificate form) := by
  unfold HasLakeinSlackOneCertificate
  infer_instance

private def IsLakeinSafeForm (form : IntegralHermitianForm) : Prop :=
  IsLakeinRootForm form ∨ IsLakeinAugmentedRootForm form ∨
    HasLakeinSlackOneCertificate form

private theorem exceptionalC01_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, 5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC02_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 1, -3⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC03_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, 1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c08
    | exact Or.inl ForbiddenSmallSuccessor.c11
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC04_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 1, 3⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC05_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, -5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC06_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, -1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c08
    | exact Or.inl ForbiddenSmallSuccessor.c11
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC07_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 3, -1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC08_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, -1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC09_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, -2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, -5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c06
    | exact Or.inl ForbiddenSmallSuccessor.c20
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC10_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 3, 1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC11_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, 1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC12_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, 2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, 5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c09
    | exact Or.inl ForbiddenSmallSuccessor.c23
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC13_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, -1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC14_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -3, -1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC15_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, -2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, -5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c06
    | exact Or.inl ForbiddenSmallSuccessor.c20
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC16_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, 1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC17_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -3, 1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC18_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, 2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, 5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c09
    | exact Or.inl ForbiddenSmallSuccessor.c23
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC19_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, 5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC20_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -1, -3⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC21_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, 1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c18
    | exact Or.inl ForbiddenSmallSuccessor.c21
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC22_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -1, 3⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC23_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, -5⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem exceptionalC24_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, -1⟩ : IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c18
    | exact Or.inl ForbiddenSmallSuccessor.c21
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

private theorem evaluate_augmented_seven_one_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 7, 1⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 3 1 IsLakeinRootCross.positiveThreePositiveOne)
    (1 : GaussianInt) (Or.inl rfl)
  have identity :
      (⟨8, 6, 7, 1⟩ : IntegralHermitianForm) =
        ⟨8, 6, 3 + 4 * (1 : GaussianInt).re,
          1 + 4 * (1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_seven_negative_one_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 7, -1⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 3 (-1) IsLakeinRootCross.positiveThreeNegativeOne)
    (1 : GaussianInt) (Or.inl rfl)
  have identity :
      (⟨8, 6, 7, -1⟩ : IntegralHermitianForm) =
        ⟨8, 6, 3 + 4 * (1 : GaussianInt).re,
          -1 + 4 * (1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_negative_seven_one_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -7, 1⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-3) 1 IsLakeinRootCross.negativeThreePositiveOne)
    (-1 : GaussianInt) (Or.inr (Or.inl rfl))
  have identity :
      (⟨8, 6, -7, 1⟩ : IntegralHermitianForm) =
        ⟨8, 6, -3 + 4 * (-1 : GaussianInt).re,
          1 + 4 * (-1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_negative_seven_negative_one_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -7, -1⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-3) (-1)
      IsLakeinRootCross.negativeThreeNegativeOne)
    (-1 : GaussianInt) (Or.inr (Or.inl rfl))
  have identity :
      (⟨8, 6, -7, -1⟩ : IntegralHermitianForm) =
        ⟨8, 6, -3 + 4 * (-1 : GaussianInt).re,
          -1 + 4 * (-1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_one_seven_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 1, 7⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 1 3 IsLakeinRootCross.positiveOnePositiveThree)
    imaginaryUnit (Or.inr (Or.inr (Or.inl rfl)))
  have identity :
      (⟨8, 6, 1, 7⟩ : IntegralHermitianForm) =
        ⟨8, 6, 1 + 4 * imaginaryUnit.re,
          3 + 4 * imaginaryUnit.im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_negative_one_seven_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -1, 7⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-1) 3 IsLakeinRootCross.negativeOnePositiveThree)
    imaginaryUnit (Or.inr (Or.inr (Or.inl rfl)))
  have identity :
      (⟨8, 6, -1, 7⟩ : IntegralHermitianForm) =
        ⟨8, 6, -1 + 4 * imaginaryUnit.re,
          3 + 4 * imaginaryUnit.im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_one_negative_seven_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 1, -7⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 1 (-3) IsLakeinRootCross.positiveOneNegativeThree)
    (-imaginaryUnit) (Or.inr (Or.inr (Or.inr rfl)))
  have identity :
      (⟨8, 6, 1, -7⟩ : IntegralHermitianForm) =
        ⟨8, 6, 1 + 4 * (-imaginaryUnit).re,
          -3 + 4 * (-imaginaryUnit).im⟩ := by decide
  rw [identity]
  exact transformed

private theorem evaluate_augmented_negative_one_negative_seven_nonnegative
    (value : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -1, -7⟩ : IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-1) (-3)
      IsLakeinRootCross.negativeOneNegativeThree)
    (-imaginaryUnit) (Or.inr (Or.inr (Or.inr rfl)))
  have identity :
      (⟨8, 6, -1, -7⟩ : IntegralHermitianForm) =
        ⟨8, 6, -1 + 4 * (-imaginaryUnit).re,
          -3 + 4 * (-imaginaryUnit).im⟩ := by decide
  rw [identity]
  exact transformed

private theorem IsLakeinSafeForm.evaluate_nonnegative
    {form : IntegralHermitianForm} {value : Gaussian}
    (safe : IsLakeinSafeForm form) (valueInside : normSq value ≤ 1)
    (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ form.evaluate value := by
  rcases safe with root | augmented | slack
  · cases root
    · exact rootNonnegative (-3) (-1)
        IsLakeinRootCross.negativeThreeNegativeOne
    · exact rootNonnegative (-3) 1
        IsLakeinRootCross.negativeThreePositiveOne
    · exact rootNonnegative (-1) (-3)
        IsLakeinRootCross.negativeOneNegativeThree
    · exact rootNonnegative (-1) 3
        IsLakeinRootCross.negativeOnePositiveThree
    · exact rootNonnegative 1 (-3)
        IsLakeinRootCross.positiveOneNegativeThree
    · exact rootNonnegative 1 3
        IsLakeinRootCross.positiveOnePositiveThree
    · exact rootNonnegative 3 (-1)
        IsLakeinRootCross.positiveThreeNegativeOne
    · exact rootNonnegative 3 1
        IsLakeinRootCross.positiveThreePositiveOne
  · cases augmented
    · exact evaluate_augmented_seven_one_nonnegative value rootNonnegative
    · exact evaluate_augmented_seven_negative_one_nonnegative value
        rootNonnegative
    · exact evaluate_augmented_negative_seven_one_nonnegative value
        rootNonnegative
    · exact evaluate_augmented_negative_seven_negative_one_nonnegative value
        rootNonnegative
    · exact evaluate_augmented_one_seven_nonnegative value rootNonnegative
    · exact evaluate_augmented_negative_one_seven_nonnegative value
        rootNonnegative
    · exact evaluate_augmented_one_negative_seven_nonnegative value
        rootNonnegative
    · exact evaluate_augmented_negative_one_negative_seven_nonnegative value
        rootNonnegative
  · change
      0 < form.radial + 1 ∧
        0 ≤ (form.constant - 1) * (form.radial + 1) -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross) at slack
    have scaleCast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
        1 (form.radial + 1)).2 (by omega)
    have scalePositive : 0 < (form.radial : Coordinate) + 1 := by
      have onePositive : (0 : Coordinate) < 1 := by decide
      apply onePositive.trans_le
      simpa only [Int.cast_one, Int.cast_add] using scaleCast
    have gapCast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct 0
        ((form.constant - 1) * (form.radial + 1) -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross))).2 slack.2
    have determinantGap :
        0 ≤ ((form.constant : Coordinate) - 1) *
            ((form.radial : Coordinate) + 1) -
          ((form.realCross : Coordinate) ^ 2 +
            (form.imaginaryCross : Coordinate) ^ 2) := by
      simpa only [Int.cast_zero, Int.cast_sub, Int.cast_one, QuotientFreeRing.intCast_mul,
        Int.cast_add, pow_two] using gapCast
    exact IntegralHermitianForm.evaluate_nonnegative_of_slack_one
      form value valueInside scalePositive determinantGap

private theorem exceptional_second_pullback_classification_of_small
    {form : IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt)
    (previousNorm : 2 ≤ normNat previousDigit)
    (small : normNat previousDigit < 11) :
    IsForbiddenSmallSuccessorPair previousDigit followingDigit ∨
      IsLakeinSafeForm (form.pullback previousDigit) := by
  have digitSmall := isSmallPreviousDigit_of_norm_bounds previousDigit
    previousNorm small
  cases exceptional
  · exact exceptionalC01_second_classification previousDigit digitSmall
  · exact exceptionalC02_second_classification previousDigit digitSmall
  · exact exceptionalC03_second_classification previousDigit digitSmall
  · exact exceptionalC04_second_classification previousDigit digitSmall
  · exact exceptionalC05_second_classification previousDigit digitSmall
  · exact exceptionalC06_second_classification previousDigit digitSmall
  · exact exceptionalC07_second_classification previousDigit digitSmall
  · exact exceptionalC08_second_classification previousDigit digitSmall
  · exact exceptionalC09_second_classification previousDigit digitSmall
  · exact exceptionalC10_second_classification previousDigit digitSmall
  · exact exceptionalC11_second_classification previousDigit digitSmall
  · exact exceptionalC12_second_classification previousDigit digitSmall
  · exact exceptionalC13_second_classification previousDigit digitSmall
  · exact exceptionalC14_second_classification previousDigit digitSmall
  · exact exceptionalC15_second_classification previousDigit digitSmall
  · exact exceptionalC16_second_classification previousDigit digitSmall
  · exact exceptionalC17_second_classification previousDigit digitSmall
  · exact exceptionalC18_second_classification previousDigit digitSmall
  · exact exceptionalC19_second_classification previousDigit digitSmall
  · exact exceptionalC20_second_classification previousDigit digitSmall
  · exact exceptionalC21_second_classification previousDigit digitSmall
  · exact exceptionalC22_second_classification previousDigit digitSmall
  · exact exceptionalC23_second_classification previousDigit digitSmall
  · exact exceptionalC24_second_classification previousDigit digitSmall

private theorem FirstExceptionalHermitian.pullback_nonnegative_of_small
    {form : IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt)
    (previousNorm : 2 ≤ normNat previousDigit)
    (small : normNat previousDigit < 11)
    (notForbidden :
      ¬ ForbiddenSmallSuccessor previousDigit followingDigit)
    (value : Gaussian) (valueInside : normSq value ≤ 1)
    (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (form.pullback previousDigit).evaluate value := by
  rcases exceptional_second_pullback_classification_of_small exceptional
      previousDigit previousNorm small with forbidden | safe
  · exact (notForbidden forbidden).elim
  · exact safe.evaluate_nonnegative valueInside rootNonnegative

/-- Every exceptional first pullback is nonnegative after the preceding
Hurwitz step.  Large preceding digits are settled by the determinant
certificate; the finitely many small digits are exactly the preceding table,
with the impossible entries removed by Hurwitz succession. -/
theorem FirstExceptionalHermitian.pullback_nonnegative
    {form : IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt)
    (previousNorm : 2 ≤ normNat previousDigit)
    (notForbidden :
      ¬ ForbiddenSmallSuccessor previousDigit followingDigit)
    (value : Gaussian) (valueInside : normSq value ≤ 1)
    (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (form.pullback previousDigit).evaluate value := by
  by_cases large : 11 ≤ normNat previousDigit
  · exact exceptional.pullback_nonnegative_of_large previousDigit large value
      valueInside
  · exact exceptional.pullback_nonnegative_of_small previousDigit previousNorm
      (Nat.lt_of_not_ge large) notForbidden value valueInside rootNonnegative

/-- The affine denominator in one backward-ratio step cannot vanish.  The
proof uses only the strict growth of the two displayed continuant
denominators and the finite lower bound on the next Hurwitz digit. -/
theorem denominatorRatio_step_sum_ne_zero
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0) :
    toGaussian (digit (next stage.quotient nonterminal)) +
        stage.denominatorRatio ≠ 0 := by
  let coefficient := digit (next stage.quotient nonterminal)
  intro sumZero
  have ratioIdentity :
      stage.denominatorRatio = -(toGaussian coefficient) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · have realZero := congrArg
        RFAP.ConstructiveGaussian.Gaussian.re sumZero
      change (coefficient.re : Coordinate) +
          stage.denominatorRatio.re = 0 at realZero
      calc
        stage.denominatorRatio.re =
            ((coefficient.re : Coordinate) +
                stage.denominatorRatio.re) -
              (coefficient.re : Coordinate) := by ring1
        _ = 0 - (coefficient.re : Coordinate) := by rw [realZero]
        _ = (-(toGaussian coefficient)).re := by
          simp only [RFAP.ConstructiveGaussian.Gaussian.neg_re, toGaussian]
          ring1
    · have imaginaryZero := congrArg
        RFAP.ConstructiveGaussian.Gaussian.im sumZero
      change (coefficient.im : Coordinate) +
          stage.denominatorRatio.im = 0 at imaginaryZero
      calc
        stage.denominatorRatio.im =
            ((coefficient.im : Coordinate) +
                stage.denominatorRatio.im) -
              (coefficient.im : Coordinate) := by ring1
        _ = 0 - (coefficient.im : Coordinate) := by rw [imaginaryZero]
        _ = (-(toGaussian coefficient)).im := by
          simp only [RFAP.ConstructiveGaussian.Gaussian.neg_im, toGaussian]
          ring1
  have coefficientNorm : 2 ≤ normNat coefficient :=
    two_le_next_digit_normNat stage.quotient nonterminal
  have coefficientNormCast :
      (2 : Coordinate) ≤ normSq (toGaussian coefficient) := by
    rw [normSq_toGaussian]
    exact RFAP.ConstructiveFraction.natCast_le_direct coefficientNorm
  have ratioAtLeastOne :
      (1 : Coordinate) ≤ normSq stage.denominatorRatio := by
    rw [ratioIdentity, normSq_neg]
    exact (show (1 : Coordinate) ≤ 2 by decide).trans coefficientNormCast
  exact (not_lt_of_ge ratioAtLeastOne)
    (denominatorRatio_normSq_lt_one_of_generated generated)

/-- Nonnegativity of a pulled-back Hermitian form transports through one
explicit Hurwitz advance. -/
theorem IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
    (form : IntegralHermitianForm)
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (pullbackNonnegative :
      0 ≤ (form.pullback
        (digit (next stage.quotient nonterminal))).evaluate
          stage.denominatorRatio) :
    0 ≤ form.evaluate
      (Stage.denominatorRatio
        (RFAP.HurwitzTrace.advanceStage stage nonterminal)) := by
  let coefficient := digit (next stage.quotient nonterminal)
  let sum := toGaussian coefficient + stage.denominatorRatio
  have sumNonzero : sum ≠ 0 := by
    exact denominatorRatio_step_sum_ne_zero generated nonterminal
  have normPositive : 0 < normSq sum := normSq_pos sumNonzero
  have transformed := form.evaluate_pullback_mul_normSq coefficient
    stage.denominatorRatio sumNonzero
  have productNonnegative :
      0 ≤ form.evaluate sum⁻¹ * normSq sum := by
    rw [transformed]
    exact pullbackNonnegative
  have evaluatedNonnegative : 0 ≤ form.evaluate sum⁻¹ := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := normSq sum) _ normPositive
    calc
      0 * normSq sum = 0 := by ring1
      _ ≤ form.evaluate sum⁻¹ * normSq sum := productNonnegative
  rw [advanceStage_denominatorRatio stage generated nonterminal]
  exact evaluatedNonnegative

private theorem lakeinRootFormsNonnegative_zero :
    LakeinRootFormsNonnegative 0 := by
  intro realCross imaginaryCross root
  cases root <;>
    decide

private theorem FirstExceptionalHermitian.evaluate_zero_nonnegative
    {form : IntegralHermitianForm} {coefficient : GaussianInt}
    (exceptional : FirstExceptionalHermitian form coefficient) :
    0 ≤ form.evaluate 0 := by
  cases exceptional <;> decide

private theorem root_pullback_nonnegative_at_zero
    {realCross imaginaryCross : Int}
    (root : IsLakeinRootCross realCross imaginaryCross)
    (coefficient : GaussianInt) (coefficientNorm : 2 ≤ normNat coefficient) :
    0 ≤ ((lakeinRootForm realCross imaginaryCross).pullback coefficient).evaluate
      0 := by
  rcases root_pullback_constant_gap_or_exceptional root coefficient
      coefficientNorm with constantGap | exceptional
  · exact
      IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
        (lakeinRootForm realCross imaginaryCross) coefficient 0
        (by decide) (by
          change (0 : Coordinate) < 4 + 1
          decide)
        (lakeinRootForm_determinant root) constantGap
  · exact exceptional.evaluate_zero_nonnegative

private theorem firstAdvance_lakeinRootFormsNonnegative
    (source : Fraction) (nonterminal : remainder source ≠ 0) :
    LakeinRootFormsNonnegative
      (Stage.denominatorRatio
        (RFAP.HurwitzTrace.advanceStage
          (RFAP.HurwitzTrace.firstStage source) nonterminal)) := by
  intro realCross imaginaryCross root
  apply IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
    (lakeinRootForm realCross imaginaryCross) Generated.first nonterminal
  rw [firstStage_denominatorRatio]
  exact root_pullback_nonnegative_at_zero root _
    (two_le_next_digit_normNat source nonterminal)

/-- Assuming the root forms at one generated stage, the explicit
two-successor classification establishes them two stages later. -/
private theorem lakeinRootFormsNonnegative_two_advances
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (nextNonterminal :
      remainder
        (RFAP.HurwitzTrace.advanceStage stage nonterminal).quotient ≠ 0)
    (rootNonnegative :
      LakeinRootFormsNonnegative stage.denominatorRatio) :
    LakeinRootFormsNonnegative
      (Stage.denominatorRatio
        (RFAP.HurwitzTrace.advanceStage
          (RFAP.HurwitzTrace.advanceStage stage nonterminal)
          nextNonterminal)) := by
  let middle := RFAP.HurwitzTrace.advanceStage stage nonterminal
  let previousDigit := digit (next stage.quotient nonterminal)
  let followingDigit := digit (next middle.quotient nextNonterminal)
  have middleGenerated : Generated source middle :=
    Generated.advance generated nonterminal
  have baseInside : normSq stage.denominatorRatio ≤ 1 :=
    (denominatorRatio_normSq_lt_one_of_generated generated).le
  have middleInside : normSq (Stage.denominatorRatio middle) ≤ 1 :=
    (denominatorRatio_normSq_lt_one_of_generated middleGenerated).le
  have previousNorm : 2 ≤ normNat previousDigit := by
    exact two_le_next_digit_normNat stage.quotient nonterminal
  have followingNorm : 2 ≤ normNat followingDigit := by
    exact two_le_next_digit_normNat middle.quotient nextNonterminal
  have notForbidden :
      ¬ ForbiddenSmallSuccessor previousDigit followingDigit := by
    change ¬ ForbiddenSmallSuccessor
      (digit (next stage.quotient nonterminal))
      (digit (next (next stage.quotient nonterminal) nextNonterminal))
    exact not_forbiddenSmallSuccessor stage.quotient nonterminal
      nextNonterminal
  intro realCross imaginaryCross root
  have firstPullbackNonnegative :
      0 ≤ ((lakeinRootForm realCross imaginaryCross).pullback
        followingDigit).evaluate (Stage.denominatorRatio middle) := by
    rcases root_pullback_constant_gap_or_exceptional root followingDigit
        followingNorm with constantGap | exceptional
    · exact
        IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
          (lakeinRootForm realCross imaginaryCross) followingDigit
          (Stage.denominatorRatio middle) middleInside (by
            change (0 : Coordinate) < 4 + 1
            decide)
          (lakeinRootForm_determinant root) constantGap
    · have secondPullbackNonnegative :
          0 ≤ (((lakeinRootForm realCross imaginaryCross).pullback
            followingDigit).pullback previousDigit).evaluate
              stage.denominatorRatio := by
        exact exceptional.pullback_nonnegative previousDigit previousNorm
          notForbidden stage.denominatorRatio baseInside rootNonnegative
      have transported :=
        IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
          ((lakeinRootForm realCross imaginaryCross).pullback followingDigit)
          generated nonterminal secondPullbackNonnegative
      exact transported
  exact IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
    (lakeinRootForm realCross imaginaryCross) middleGenerated nextNonterminal
    firstPullbackNonnegative

/-- The induction invariant remembers the root inequalities both at the
current generated stage and after each possible next advance.  This makes
the two-step exceptional calculation line up exactly with the unary
`Generated` recursion. -/
private def LakeinRootStageInvariant {source : Fraction}
    (stage : Stage source) : Prop :=
  LakeinRootFormsNonnegative stage.denominatorRatio ∧
    ∀ nonterminal : remainder stage.quotient ≠ 0,
      LakeinRootFormsNonnegative
        (Stage.denominatorRatio
          (RFAP.HurwitzTrace.advanceStage stage nonterminal))

private theorem lakeinRootStageInvariant_of_generated
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) :
    LakeinRootStageInvariant stage := by
  induction generated with
  | first =>
      constructor
      · rw [firstStage_denominatorRatio]
        exact lakeinRootFormsNonnegative_zero
      · intro nonterminal
        exact firstAdvance_lakeinRootFormsNonnegative source nonterminal
  | @advance previousStage generated previousNonterminal inductionHypothesis =>
      constructor
      · exact inductionHypothesis.2 previousNonterminal
      · intro nextNonterminal
        exact lakeinRootFormsNonnegative_two_advances generated
          previousNonterminal nextNonterminal inductionHypothesis.1

/-- All eight quadrance-five/diagonal root forms are nonnegative at every
stage produced by the finite Hurwitz trace. -/
theorem lakeinRootFormsNonnegative_of_generated
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) :
    LakeinRootFormsNonnegative stage.denominatorRatio :=
  (lakeinRootStageInvariant_of_generated generated).1

private theorem normFive_diagonal_factor_identity
    (ratio : Gaussian) (s t : GaussianInt)
    (sNorm : normNat s = 5) (tNorm : normNat t = 2) :
    normSq (toGaussian s + toGaussian t * ratio) =
      1 +
        (lakeinRootForm
          (s.re * t.re + s.im * t.im)
          (-s.re * t.im + s.im * t.re)).evaluate ratio := by
  have sNormIdentity : normSq (toGaussian s) = 5 := by
    rw [normSq_toGaussian, sNorm]
    rfl
  have tNormIdentity : normSq (toGaussian t) = 2 := by
    rw [normSq_toGaussian, tNorm]
    rfl
  calc
    normSq (toGaussian s + toGaussian t * ratio) =
        normSq (toGaussian s) + normSq (toGaussian t) * normSq ratio +
          2 *
            (((s.re * t.re + s.im * t.im : Int) : Coordinate) * ratio.re +
              ((-s.re * t.im + s.im * t.re : Int) : Coordinate) *
                ratio.im) := by
      simp only [normSq, toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        Int.cast_add, QuotientFreeRing.intCast_mul, Int.cast_neg]
      ring1
    _ = 5 + 2 * normSq ratio +
          2 *
            (((s.re * t.re + s.im * t.im : Int) : Coordinate) * ratio.re +
              ((-s.re * t.im + s.im * t.re : Int) : Coordinate) *
                ratio.im) := by
      rw [sNormIdentity, tNormIdentity]
    _ = 1 +
        (lakeinRootForm
          (s.re * t.re + s.im * t.im)
          (-s.re * t.im + s.im * t.re)).evaluate ratio := by
      simp only [IntegralHermitianForm.evaluate, lakeinRootForm,
        finiteHermitianForm, Int.cast_ofNat, Int.cast_add, QuotientFreeRing.intCast_mul,
        Int.cast_neg]
      ring1

private theorem normFive_diagonal_cross_isLakeinRoot
    {s t : GaussianInt} (sNorm : normNat s = 5)
    (tNorm : normNat t = 2) :
    IsLakeinRootCross
      (s.re * t.re + s.im * t.im)
      (-s.re * t.im + s.im * t.re) := by
  have sCases := normFive_cases_of_normNat_eq_five sNorm
  have tCases := isDiagonal_of_normNat_eq_two tNorm
  rcases sCases with sCase | sCase | sCase | sCase | sCase | sCase |
      sCase | sCase <;>
    rcases tCases with tCase | tCase | tCase | tCase <;>
    subst s <;> subst t
  all_goals first
    | exact IsLakeinRootCross.negativeThreeNegativeOne
    | exact IsLakeinRootCross.negativeThreePositiveOne
    | exact IsLakeinRootCross.negativeOneNegativeThree
    | exact IsLakeinRootCross.negativeOnePositiveThree
    | exact IsLakeinRootCross.positiveOneNegativeThree
    | exact IsLakeinRootCross.positiveOnePositiveThree
    | exact IsLakeinRootCross.positiveThreeNegativeOne
    | exact IsLakeinRootCross.positiveThreePositiveOne

/-- The eight root-form inequalities are precisely the exterior certificate
for every quadrance-five coefficient paired with a diagonal coefficient. -/
theorem one_le_normSq_normFive_add_diagonal_mul_of_rootForms
    (ratio : Gaussian) (rootNonnegative : LakeinRootFormsNonnegative ratio)
    (s t : GaussianInt) (sNorm : normNat s = 5)
    (tNorm : normNat t = 2) :
    1 ≤ normSq (toGaussian s + toGaussian t * ratio) := by
  let realCross := s.re * t.re + s.im * t.im
  let imaginaryCross := -s.re * t.im + s.im * t.re
  have root : IsLakeinRootCross realCross imaginaryCross :=
    normFive_diagonal_cross_isLakeinRoot sNorm tNorm
  have rootBound := rootNonnegative realCross imaginaryCross root
  calc
    (1 : Coordinate) = 1 + 0 := by ring1
    _ ≤ 1 + (lakeinRootForm realCross imaginaryCross).evaluate ratio :=
      by
        have shifted :=
          RFAP.ConstructiveFraction.add_le_add_right_direct rootBound 1
        calc
          (1 : Coordinate) + 0 = 0 + 1 := by ring1
          _ ≤ (lakeinRootForm realCross imaginaryCross).evaluate ratio + 1 :=
            shifted
          _ = 1 + (lakeinRootForm realCross imaginaryCross).evaluate ratio := by
            ring1
    _ = normSq (toGaussian s + toGaussian t * ratio) := by
      exact (normFive_diagonal_factor_identity ratio s t sNorm tNorm).symm

/-- Root-form nonnegativity supplies the outstanding quadrance-five
denominator comparison at a generated stage. -/
theorem normFiveDenominatorSafe_of_rootForms
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (rootNonnegative :
      LakeinRootFormsNonnegative stage.denominatorRatio) :
    NormFiveDenominatorSafe stage := by
  intro s t sNorm tNorm
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  let currentValue := toGaussian stage.current.denominator
  let factor := toGaussian s + toGaussian t * stage.denominatorRatio
  have factorExterior : 1 ≤ normSq factor := by
    dsimp only [factor]
    exact one_le_normSq_normFive_add_diagonal_mul_of_rootForms
      stage.denominatorRatio rootNonnegative s t sNorm tNorm
  have currentNormNonnegative : 0 ≤ normSq currentValue := normSq_nonneg _
  have scaledExterior :
      1 * normSq currentValue ≤ normSq factor * normSq currentValue :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      factorExterior currentNormNonnegative
  have factorIdentity :
      factor * currentValue =
        toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator) := by
    dsimp only [factor, currentValue]
    rw [toGaussian_add, toGaussian_mul, toGaussian_mul,
      ← denominatorRatio_mul_current stage currentNonzero]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  calc
    (normNat stage.current.denominator : Coordinate) =
        normSq currentValue := (normSq_toGaussian _).symm
    _ = 1 * normSq currentValue := by ring1
    _ ≤ normSq factor * normSq currentValue := scaledExterior
    _ = normSq (factor * currentValue) := by rw [normSq_mul]
    _ = normSq
        (toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator)) := by rw [factorIdentity]
    _ = (normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) : Coordinate) :=
      normSq_toGaussian _

/-- Every generated Hurwitz stage satisfies the exceptional denominator
certificate required by Lakein's comparison. -/
theorem normFiveDenominatorSafe_of_generated
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) :
    NormFiveDenominatorSafe stage :=
  normFiveDenominatorSafe_of_rootForms generated
    (lakeinRootFormsNonnegative_of_generated generated)

/-- A terminal generated stage reconstructs the displayed rational source
exactly. -/
theorem Stage.current_error_eq_zero_of_terminal
    {source : Fraction} (stage : Stage source)
    (terminal : remainder stage.quotient = 0) :
    error source.value stage.current = 0 := by
  have residualZero : residual stage.quotient = 0 := by
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      stage.quotient.denominatorGaussianNonzero
    calc
      residual stage.quotient *
            toGaussian stage.quotient.denominator =
          toGaussian (remainder stage.quotient) :=
        (remainder_toGaussian stage.quotient).symm
      _ = 0 := by rw [terminal, toGaussian_zero]
      _ = 0 * toGaussian stage.quotient.denominator := by
        rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul]
  have relation := stage.error_add_residual_mul_previous_eq_zero
  rw [residualZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero] at relation
  exact relation

/-- Lakein's comparison at a nonterminal generated stage. -/
theorem Stage.atLeastAsGoodAs_of_generated_nonterminal
    {source : Fraction} (stage : Stage source)
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (competitor : RFAP.HurwitzRational.ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      normNat competitor.denominator < normNat stage.current.denominator) :
    AtLeastAsGoodAs source.value stage.current competitor := by
  exact stage.atLeastAsGoodAs_of_generated_of_normFiveDenominatorSafe
    generated (normFiveDenominatorSafe_of_generated generated) nonterminal
    competitor competitorDenominatorNonzero denominatorSmaller

/-- **Finite Lakein inequality.**  Every displayed Hurwitz convergent is at
least as good as any Gaussian-rational competitor with strictly smaller
denominator quadrance.  At the terminal stage the displayed convergent is
exact; every earlier stage is covered by the finite root-form invariant. -/
theorem Stage.atLeastAsGoodAs_of_generated
    {source : Fraction} (stage : Stage source)
    (generated : Generated source stage)
    (competitor : RFAP.HurwitzRational.ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      normNat competitor.denominator < normNat stage.current.denominator) :
    AtLeastAsGoodAs source.value stage.current competitor := by
  by_cases terminal : remainder stage.quotient = 0
  · have currentErrorZero := stage.current_error_eq_zero_of_terminal terminal
    rw [AtLeastAsGoodAs, currentErrorZero, normSq_zero]
    exact normSq_nonneg _
  · exact stage.atLeastAsGoodAs_of_generated_nonterminal generated terminal
      competitor competitorDenominatorNonzero denominatorSmaller

/-- Every generated stage satisfies the unconditional weak lower-height
best-approximation predicate. -/
theorem Stage.isWeakLowerBest_of_generated
    {source : Fraction} (stage : Stage source)
    (generated : Generated source stage) :
    RFAP.BestApproximation.IsWeakLowerBest source.value stage.current := by
  refine ⟨current_denominator_ne_zero_of_generated generated, ?_⟩
  intro competitor competitorNonzero denominatorSmaller
  change AtLeastAsGoodAs source.value stage.current competitor
  exact stage.atLeastAsGoodAs_of_generated generated competitor
    competitorNonzero denominatorSmaller

/-- The terminal Hurwitz pair is not merely weakly optimal: its zero error
and adjacent unit determinant make it a genuine best approximation.  Any
smaller exact competitor would force its denominator to be a nonzero
Gaussian-integer multiple of the terminal denominator. -/
theorem Stage.isBest_of_generated_of_terminal
    {source : Fraction} (stage : Stage source)
    (generated : Generated source stage)
    (terminal : remainder stage.quotient = 0) :
    RFAP.BestApproximation.IsBest source.value stage.current := by
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  have currentErrorZero := stage.current_error_eq_zero_of_terminal terminal
  refine ⟨currentNonzero, ?_, ?_⟩
  · intro competitor competitorNonzero denominatorSmaller
    rw [RFAP.BestApproximation.errorQuadrance, currentErrorZero, normSq_zero]
    apply normSq_pos
    intro competitorErrorZero
    have determinantGaussianZero :
        toGaussian (determinant stage.current competitor) = 0 := by
      rw [RFAP.HurwitzTrace.determinant_eq_denominator_mul_error_sub,
        competitorErrorZero, currentErrorZero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.zero_re,
          RFAP.ConstructiveGaussian.Gaussian.zero_im] <;>
        ring1
    have determinantZero : determinant stage.current competitor = 0 :=
      toGaussian_eq_zero.mp determinantGaussianZero
    have denominatorDecomposition := competitor_denominator_decomposition
      (competitor := competitor) stage.unitDeterminant
    simp only [previousCoefficient, determinantZero,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_zero,
      RFAP.ConstructiveGaussianHeight.GaussianInt.zero_mul,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero] at denominatorDecomposition
    have coefficientNonzero :
        currentCoefficient stage.current stage.previous competitor ≠ 0 := by
      intro coefficientZero
      rw [coefficientZero,
        RFAP.ConstructiveGaussianHeight.GaussianInt.zero_mul] at denominatorDecomposition
      exact competitorNonzero denominatorDecomposition.symm
    have coefficientPositive := normNat_pos coefficientNonzero
    have currentNoLarger :
        normNat stage.current.denominator ≤ normNat competitor.denominator := by
      calc
        normNat stage.current.denominator =
            1 * normNat stage.current.denominator :=
          (Nat.one_mul _).symm
        _ ≤ normNat
              (currentCoefficient stage.current stage.previous competitor) *
              normNat stage.current.denominator :=
          Nat.mul_le_mul_right _ coefficientPositive
        _ = normNat competitor.denominator := by
          rw [← normNat_mul, denominatorDecomposition]
    exact (not_lt_of_ge currentNoLarger denominatorSmaller).elim
  · intro competitor _ _
    rw [RFAP.BestApproximation.errorQuadrance, currentErrorZero, normSq_zero]
    exact normSq_nonneg _

/-- Every displayed rational source has a best approximation, witnessed
constructively by the terminal pair of its executable Hurwitz trace. -/
theorem exists_bestApproximation (source : Fraction) :
    ∃ pair : RFAP.HurwitzRational.ConvergentPair,
      RFAP.BestApproximation.IsBest source.value pair := by
  obtain ⟨terminalStage, member, terminal⟩ :=
    RFAP.HurwitzTrace.exists_terminal_mem_stages source
  have generated := generated_of_mem_stages member
  exact ⟨terminalStage.current,
    RFAP.HurwitzGeometry.Stage.isBest_of_generated_of_terminal
      terminalStage generated terminal⟩

/-- The sound-and-complete finite all-best selector always returns at least
one displayed pair. -/
theorem allBest_nonempty (source : Fraction) :
    RFAP.BestApproximation.allBest source ≠ [] := by
  obtain ⟨pair, best⟩ := exists_bestApproximation source
  have member :=
    (RFAP.BestApproximation.mem_allBest_iff_isBest source pair).mpr best
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

private theorem int_square_nonnegative (x : Int) : 0 ≤ x * x := by
  by_cases nonnegative : 0 ≤ x
  · exact Int.mul_nonneg nonnegative nonnegative
  · have nonpositive : x ≤ 0 := Int.le_of_lt (Int.lt_of_not_ge nonnegative)
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

private theorem twice_int_le_sum_squares {x y : Int}
    (twoLe : 2 ≤ x * x + y * y) : 2 * x ≤ x * x + y * y := by
  by_cases xAtLeastTwo : 2 ≤ x
  · have xNonnegative : 0 ≤ x := (by decide : (0 : Int) ≤ 2).trans
      xAtLeastTwo
    have differenceNonnegative : 0 ≤ x - 2 := by
      have shifted := Int.add_le_add_right xAtLeastTwo (-2)
      convert shifted using 1 <;> ring1
    have productNonnegative : 0 ≤ x * (x - 2) :=
      Int.mul_nonneg xNonnegative differenceNonnegative
    have productIdentity : x * (x - 2) = x * x - 2 * x := by ring1
    rw [productIdentity] at productNonnegative
    have ySquareNonnegative := int_square_nonnegative y
    have twiceLeSquare : 2 * x ≤ x * x := by
      have shifted := Int.add_le_add_right productNonnegative (2 * x)
      convert shifted using 1 <;> ring1
    have squareLeSum : x * x ≤ x * x + y * y := by
      have shifted := Int.add_le_add_left ySquareNonnegative (x * x)
      simpa only [Int.add_zero] using shifted
    exact twiceLeSquare.trans squareLeSum
  · by_cases xAtMostMinusTwo : x ≤ -2
    · have sumNonnegative : 0 ≤ x * x + y * y :=
        Int.add_nonneg (int_square_nonnegative x) (int_square_nonnegative y)
      have xNonpositive : x ≤ 0 :=
        xAtMostMinusTwo.trans (by decide)
      have twiceNonpositive : 2 * x ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by decide) xNonpositive
      exact twiceNonpositive.trans sumNonnegative
    · have lower : -(2 : Int) < x := Int.lt_of_not_ge xAtMostMinusTwo
      have upper : x < 2 := Int.lt_of_not_ge xAtLeastTwo
      have minusOneLe : (-1 : Int) ≤ x := by
        change (-(2 : Int) + 1) ≤ x
        exact Int.add_one_le_iff.mpr lower
      have oneUpper : x ≤ (1 : Int) := by
        change x ≤ (2 : Int) - 1
        exact Int.le_sub_one_iff.mpr upper
      by_cases minusOne : x = -1
      · subst x
        calc
          (2 : Int) * -1 ≤ 0 := by decide
          _ ≤ -1 * -1 + y * y :=
            Int.add_nonneg (by decide) (int_square_nonnegative y)
      have zeroLe : (0 : Int) ≤ x := by
        change (-1 : Int) + 1 ≤ x
        exact Int.add_one_le_iff.mpr
          (lt_of_le_of_ne minusOneLe (Ne.symm minusOne))
      by_cases zero : x = 0
      · subst x
        simpa only [Int.mul_zero, Int.zero_mul, Int.zero_add] using
          int_square_nonnegative y
      have oneLe : (1 : Int) ≤ x := by
        change (0 : Int) + 1 ≤ x
        exact Int.add_one_le_iff.mpr
          (lt_of_le_of_ne zeroLe (Ne.symm zero))
      have xOne : x = 1 := Int.le_antisymm oneUpper oneLe
      subst x
      simpa only [Int.mul_one, Int.one_mul] using twoLe

private theorem neg_sum_squares_le_twice_int {x y : Int}
    (twoLe : 2 ≤ x * x + y * y) :
    -(x * x + y * y) ≤ 2 * x := by
  have reflectedNorm : (-x) * (-x) + y * y = x * x + y * y := by ring1
  have reflectedTwoLe : 2 ≤ (-x) * (-x) + y * y := by
    rw [reflectedNorm]
    exact twoLe
  have upper := twice_int_le_sum_squares reflectedTwoLe
  rw [reflectedNorm] at upper
  have negated := Int.neg_le_neg upper
  calc
    -(x * x + y * y) ≤ -(2 * -x) := negated
    _ = 2 * x := by ring1

private theorem half_mul_two_mul (value : Coordinate) :
    (1 / 2 : Coordinate) * (2 * value) = value := by
  calc
    (1 / 2 : Coordinate) * (2 * value) =
        ((1 / 2 : Coordinate) * 2) * value :=
      (_root_.mul_assoc _ _ _).symm
    _ = 1 * value := by rw [show (1 / 2 : Coordinate) * 2 = 1 by decide]
    _ = value := one_mul _

private theorem half_scaled_bounds {value bound : Coordinate}
    (lower : -bound ≤ 2 * value) (upper : 2 * value ≤ bound) :
    -(1 / 2 : Coordinate) * bound ≤ value ∧
      value ≤ (1 / 2 : Coordinate) * bound := by
  have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := by decide
  have scaledLower :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      lower halfNonnegative
  have scaledUpper :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      upper halfNonnegative
  constructor
  · calc
      -(1 / 2 : Coordinate) * bound =
          (1 / 2 : Coordinate) * (-bound) := by ring1
      _ ≤ (1 / 2 : Coordinate) * (2 * value) := scaledLower
      _ = value := half_mul_two_mul value
  · calc
      value = (1 / 2 : Coordinate) * (2 * value) :=
        (half_mul_two_mul value).symm
      _ ≤ (1 / 2 : Coordinate) * bound := scaledUpper

private theorem div_half_bounds {value bound : Coordinate}
    (boundPositive : 0 < bound)
    (scaledBounds :
      -(1 / 2 : Coordinate) * bound ≤ value ∧
        value ≤ (1 / 2 : Coordinate) * bound) :
    -(1 / 2 : Coordinate) ≤ value / bound ∧
      value / bound ≤ (1 / 2 : Coordinate) := by
  exact
    ⟨(RFAP.ConstructiveFraction.le_div_iff_pos boundPositive).2
        scaledBounds.1,
      (RFAP.ConstructiveFraction.div_le_iff_pos boundPositive).2
        scaledBounds.2⟩

/-- Every reciprocal of a Gaussian integer of quadrance at least two lies
coordinatewise in the half-square. -/
theorem inverse_integer_coordinate_bounds {value : GaussianInt}
    (twoLe : 2 ≤ normNat value) :
    -(1 / 2 : Coordinate) ≤ (toGaussian value)⁻¹.re ∧
      (toGaussian value)⁻¹.re ≤ (1 / 2 : Coordinate) ∧
      -(1 / 2 : Coordinate) ≤ (toGaussian value)⁻¹.im ∧
      (toGaussian value)⁻¹.im ≤ (1 / 2 : Coordinate) := by
  have normIntTwoLe : (2 : Int) ≤ normInt value := by
    rw [normInt_eq_natCast_normNat]
    exact Int.ofNat_le.mpr twoLe
  have realUpperInt : 2 * value.re ≤ normInt value := by
    exact twice_int_le_sum_squares normIntTwoLe
  have realLowerInt : -normInt value ≤ 2 * value.re := by
    exact neg_sum_squares_le_twice_int normIntTwoLe
  have imaginaryUpperInt : 2 * value.im ≤ normInt value := by
    change 2 * value.im ≤
      value.re * value.re + value.im * value.im
    calc
      2 * value.im ≤ value.im * value.im + value.re * value.re :=
        twice_int_le_sum_squares (x := value.im) (y := value.re) (by
          rw [_root_.add_comm]
          exact normIntTwoLe)
      _ = value.re * value.re + value.im * value.im := by ring1
  have imaginaryLowerInt : -normInt value ≤ 2 * value.im := by
    change -(value.re * value.re + value.im * value.im) ≤ 2 * value.im
    calc
      -(value.re * value.re + value.im * value.im) =
          -(value.im * value.im + value.re * value.re) := by ring1
      _ ≤ 2 * value.im :=
        neg_sum_squares_le_twice_int (x := value.im) (y := value.re) (by
          rw [_root_.add_comm]
          exact normIntTwoLe)
  have normPositiveNat : 0 < normNat value := lt_of_lt_of_le (by decide) twoLe
  have normPositive : (0 : Coordinate) < (normNat value : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct normPositiveNat
  have normIdentity :
      normSq (toGaussian value) = (normNat value : Coordinate) :=
    normSq_toGaussian value
  have castRealUpper :
      (2 : Coordinate) * (value.re : Coordinate) ≤
        (normNat value : Coordinate) := by
    have cast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).2
        realUpperInt
    simpa only [QuotientFreeRing.intCast_mul, Int.cast_ofNat,
      normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have castRealLower :
      -(normNat value : Coordinate) ≤
        (2 : Coordinate) * (value.re : Coordinate) := by
    have cast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).2
        realLowerInt
    simpa only [Int.cast_neg, QuotientFreeRing.intCast_mul, Int.cast_ofNat,
      normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have castImaginaryUpper :
      (2 : Coordinate) * (value.im : Coordinate) ≤
        (normNat value : Coordinate) := by
    have cast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).2
        imaginaryUpperInt
    simpa only [QuotientFreeRing.intCast_mul, Int.cast_ofNat,
      normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have castImaginaryLower :
      -(normNat value : Coordinate) ≤
        (2 : Coordinate) * (value.im : Coordinate) := by
    have cast :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).2
        imaginaryLowerInt
    simpa only [Int.cast_neg, QuotientFreeRing.intCast_mul, Int.cast_ofNat,
      normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have realScaledBounds := half_scaled_bounds castRealLower castRealUpper
  have imaginaryNegLower :
      -(normNat value : Coordinate) ≤
        2 * (-(value.im : Coordinate)) := by
    have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct
      castImaginaryUpper
    calc
      -(normNat value : Coordinate) ≤
          -((2 : Coordinate) * (value.im : Coordinate)) := reversed
      _ = 2 * (-(value.im : Coordinate)) := by ring1
  have imaginaryNegUpper :
      2 * (-(value.im : Coordinate)) ≤
        (normNat value : Coordinate) := by
    have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct
      castImaginaryLower
    calc
      2 * (-(value.im : Coordinate)) =
          -((2 : Coordinate) * (value.im : Coordinate)) := by ring1
      _ ≤ -(-(normNat value : Coordinate)) := reversed
      _ = (normNat value : Coordinate) := neg_neg _
  have imaginaryScaledBounds :=
    half_scaled_bounds imaginaryNegLower imaginaryNegUpper
  have realBounds := div_half_bounds normPositive realScaledBounds
  have imaginaryBounds := div_half_bounds normPositive imaginaryScaledBounds
  rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq]
  change
    -(1 / 2 : Coordinate) ≤
        (value.re : Coordinate) / normSq (toGaussian value) ∧
      (value.re : Coordinate) / normSq (toGaussian value) ≤ 1 / 2 ∧
      -(1 / 2 : Coordinate) ≤
        -(value.im : Coordinate) / normSq (toGaussian value) ∧
      -(value.im : Coordinate) / normSq (toGaussian value) ≤ 1 / 2
  rw [normIdentity]
  exact ⟨realBounds.1, realBounds.2,
    imaginaryBounds.1, imaginaryBounds.2⟩

/-- The first noninitial denominator ratio is already in the smaller
half-square. -/
theorem firstAdvance_denominatorRatioInLakeinSquare (source : Fraction)
    (nonterminal : remainder source ≠ 0) :
    DenominatorRatioInLakeinSquare
      (RFAP.HurwitzTrace.advanceStage
      (RFAP.HurwitzTrace.firstStage source) nonterminal) := by
  unfold DenominatorRatioInLakeinSquare
  have recurrence := advanceStage_denominatorRatio
    (RFAP.HurwitzTrace.firstStage source) Generated.first nonterminal
  have digitTwoLe := two_le_next_digit_normNat source nonterminal
  have inverseBounds := inverse_integer_coordinate_bounds digitTwoLe
  change
    -(3 / 4 : Coordinate) ≤
        (Stage.denominatorRatio
          (RFAP.HurwitzTrace.advanceStage
            (RFAP.HurwitzTrace.firstStage source) nonterminal)).re ∧
      (Stage.denominatorRatio
          (RFAP.HurwitzTrace.advanceStage
            (RFAP.HurwitzTrace.firstStage source) nonterminal)).re ≤ 3 / 4 ∧
      -(3 / 4 : Coordinate) ≤
        (Stage.denominatorRatio
          (RFAP.HurwitzTrace.advanceStage
            (RFAP.HurwitzTrace.firstStage source) nonterminal)).im ∧
      (Stage.denominatorRatio
          (RFAP.HurwitzTrace.advanceStage
            (RFAP.HurwitzTrace.firstStage source) nonterminal)).im ≤ 3 / 4
  rw [recurrence]
  rw [firstStage_denominatorRatio,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]
  exact
    ⟨(show -(3 / 4 : Coordinate) ≤ -(1 / 2) by decide).trans
        inverseBounds.1,
      inverseBounds.2.1.trans (show (1 / 2 : Coordinate) ≤ 3 / 4 by decide),
      (show -(3 / 4 : Coordinate) ≤ -(1 / 2) by decide).trans
        inverseBounds.2.2.1,
      inverseBounds.2.2.2.trans
        (show (1 / 2 : Coordinate) ≤ 3 / 4 by decide)⟩

/-- The Lakein square is exactly strong enough to provide the outstanding
quadrance-five denominator certificate. -/
theorem normFiveDenominatorSafe_of_lakeinSquare
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (inside : DenominatorRatioInLakeinSquare stage) :
    NormFiveDenominatorSafe stage := by
  intro s t sNorm tNorm
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  let currentValue := toGaussian stage.current.denominator
  let factor := toGaussian s + toGaussian t * stage.denominatorRatio
  have factorExterior : 1 ≤ normSq factor := by
    dsimp only [factor]
    exact one_le_normSq_normFive_add_diagonal_mul_of_coordinate_bounds
      stage.denominatorRatio s t sNorm tNorm inside.1 inside.2.1
      inside.2.2.1 inside.2.2.2
  have currentNormNonnegative : 0 ≤ normSq currentValue := normSq_nonneg _
  have scaledExterior :
      1 * normSq currentValue ≤ normSq factor * normSq currentValue :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      factorExterior currentNormNonnegative
  have factorIdentity :
      factor * currentValue =
        toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator) := by
    dsimp only [factor, currentValue]
    rw [toGaussian_add, toGaussian_mul, toGaussian_mul,
      ← denominatorRatio_mul_current stage currentNonzero]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  calc
    (normNat stage.current.denominator : Coordinate) =
        normSq currentValue := (normSq_toGaussian _).symm
    _ = 1 * normSq currentValue := by ring1
    _ ≤ normSq factor * normSq currentValue := scaledExterior
    _ = normSq (factor * currentValue) := by rw [normSq_mul]
    _ = normSq
        (toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator)) := by rw [factorIdentity]
    _ = (normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) : Coordinate) :=
      normSq_toGaussian _

/-- The exceptional denominator comparison is automatic at the first
noninitial convergent; no succession argument is needed until the following
stage. -/
theorem firstAdvance_normFiveDenominatorSafe (source : Fraction)
    (nonterminal : remainder source ≠ 0) :
    NormFiveDenominatorSafe
      (RFAP.HurwitzTrace.advanceStage
        (RFAP.HurwitzTrace.firstStage source) nonterminal) := by
  exact normFiveDenominatorSafe_of_lakeinSquare
    (Generated.advance Generated.first nonterminal)
    (firstAdvance_denominatorRatioInLakeinSquare source nonterminal)

theorem firstStage_denominatorRatioInLakeinSquare (source : Fraction) :
    DenominatorRatioInLakeinSquare
      (RFAP.HurwitzTrace.firstStage source) := by
  unfold DenominatorRatioInLakeinSquare
  rw [firstStage_denominatorRatio]
  change -(3 / 4 : Coordinate) ≤ 0 ∧ 0 ≤ 3 / 4 ∧
    -(3 / 4 : Coordinate) ≤ 0 ∧ 0 ≤ 3 / 4
  decide

end RFAP.HurwitzGeometry
