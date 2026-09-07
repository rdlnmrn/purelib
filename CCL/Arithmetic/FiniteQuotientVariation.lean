import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian

/-!
# Constructive finite variation bounds for powers and quotients

These core estimates use only displayed Gaussian rationals and finite induction on
the exponent.  They are the quantitative kernel for constant local models of
`x^k/y` on a prepared hyperelliptic continuation cell.
-/

namespace CCL.ArithmeticFiniteQuotientVariation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- Squared Lipschitz coefficient for the displayed finite power on a region
where both squared norms are at most `radiusSq`. -/
def powerSlope (radiusSq : Coordinate) : Nat -> Coordinate
  | 0 => 0
  | exponent + 1 =>
      2 * (powerSlope radiusSq exponent * radiusSq + radiusSq ^ exponent)

theorem powerSlope_nonnegative {radiusSq : Coordinate}
    (radiusNonnegative : 0 <= radiusSq) : forall exponent,
    0 <= powerSlope radiusSq exponent
  | 0 => le_rfl
  | exponent + 1 =>
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (powerSlope_nonnegative radiusNonnegative exponent)
            radiusNonnegative)
          (RFAP.ConstructiveFraction.pow_nonneg_direct radiusNonnegative
            exponent))

/-- Finite induction gives a uniform squared variation estimate for `x^k`. -/
theorem normSq_pow_sub_pow_le {radiusSq : Coordinate}
    (radiusNonnegative : 0 <= radiusSq) : forall (exponent : Nat)
    {left right : Gaussian}, normSq left <= radiusSq ->
    normSq right <= radiusSq ->
    normSq (left ^ exponent - right ^ exponent) <=
      powerSlope radiusSq exponent * normSq (left - right)
  | 0, left, right, leftBound, rightBound => by
      rw [pow_zero, pow_zero, sub_self, normSq_zero]
      exact RFAP.ConstructiveFraction.mul_nonneg_direct
        (powerSlope_nonnegative radiusNonnegative 0)
        (normSq_nonneg (left - right))
  | exponent + 1, left, right, leftBound, rightBound => by
      have previous := normSq_pow_sub_pow_le radiusNonnegative exponent
        leftBound rightBound
      have rightPowerBound : normSq (right ^ exponent) <=
          radiusSq ^ exponent := by
        rw [normSq_pow]
        exact RFAP.ConstructiveFraction.pow_le_pow_direct
          (normSq_nonneg right) rightBound exponent
      have identity :
          left ^ (exponent + 1) - right ^ (exponent + 1) =
            (left ^ exponent - right ^ exponent) * left +
              right ^ exponent * (left - right) := by
        rw [pow_succ, pow_succ]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
          ring1
      rw [identity]
      calc
        normSq ((left ^ exponent - right ^ exponent) * left +
            right ^ exponent * (left - right)) <=
            2 *
              (normSq ((left ^ exponent - right ^ exponent) * left) +
                normSq (right ^ exponent * (left - right))) :=
          normSq_add_le_two _ _
        _ = 2 *
              (normSq (left ^ exponent - right ^ exponent) * normSq left +
                normSq (right ^ exponent) * normSq (left - right)) := by
          rw [normSq_mul, normSq_mul]
        _ <= 2 *
              ((powerSlope radiusSq exponent * normSq (left - right)) *
                  radiusSq +
                radiusSq ^ exponent * normSq (left - right)) := by
          apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          · exact add_le_add
              (RFAP.ConstructiveFraction.mul_le_mul_direct previous leftBound
                (normSq_nonneg left)
                (RFAP.ConstructiveFraction.mul_nonneg_direct
                  (powerSlope_nonnegative radiusNonnegative exponent)
                  (normSq_nonneg (left - right))))
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                rightPowerBound (normSq_nonneg (left - right)))
          · decide
        _ = powerSlope radiusSq (exponent + 1) * normSq (left - right) := by
          simp only [powerSlope]
          ring1

/-- Exact common-denominator identity for two displayed Gaussian quotients. -/
theorem div_sub_div (leftNumerator rightNumerator leftDenominator
    rightDenominator : Gaussian)
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0) :
    leftNumerator / leftDenominator -
        rightNumerator / rightDenominator =
      (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (leftDenominator * rightDenominator) := by
  have productNonzero := mul_ne_zero_direct leftNonzero rightNonzero
  apply mul_right_cancel_of_ne productNonzero
  calc
    (leftNumerator / leftDenominator -
          rightNumerator / rightDenominator) *
        (leftDenominator * rightDenominator) =
      (leftNumerator / leftDenominator * leftDenominator) *
          rightDenominator -
        (rightNumerator / rightDenominator * rightDenominator) *
          leftDenominator := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = leftNumerator * rightDenominator -
          rightNumerator * leftDenominator := by
      rw [RFAP.ExplicitField.div_mul_cancel leftNumerator leftNonzero,
        RFAP.ExplicitField.div_mul_cancel rightNumerator rightNonzero]
    _ = ((leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
            (leftDenominator * rightDenominator)) *
          (leftDenominator * rightDenominator) :=
      (RFAP.ExplicitField.div_mul_cancel _ productNonzero).symm

/-- A fully rational variation majorant for two quotients. -/
def quotientBound (numeratorSlope numeratorBound denominatorBound lowerSq
    pointMovement rootMovement : Coordinate) : Coordinate :=
  (2 * (numeratorSlope * pointMovement * denominatorBound +
    numeratorBound * rootMovement)) / (lowerSq * lowerSq)

theorem quotientBound_nonnegative
    {numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Coordinate}
    (slopeNonnegative : 0 <= numeratorSlope)
    (numeratorNonnegative : 0 <= numeratorBound)
    (denominatorNonnegative : 0 <= denominatorBound)
    (lowerNonnegative : 0 <= lowerSq)
    (pointNonnegative : 0 <= pointMovement)
    (rootNonnegative : 0 <= rootMovement) :
    0 <= quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
      pointMovement rootMovement :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct slopeNonnegative
            pointNonnegative) denominatorNonnegative)
        (RFAP.ConstructiveFraction.mul_nonneg_direct numeratorNonnegative
          rootNonnegative)))
    (RFAP.ConstructiveFraction.mul_nonneg_direct lowerNonnegative
      lowerNonnegative)

/-- Quotient variation from explicit numerator, denominator, and movement
bounds.  No limit object or global extremum enters the estimate. -/
theorem normSq_div_sub_div_le
    {leftNumerator rightNumerator leftDenominator rightDenominator : Gaussian}
    {numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Coordinate}
    (lowerPositive : 0 < lowerSq)
    (numeratorDifference :
      normSq (leftNumerator - rightNumerator) <=
        numeratorSlope * pointMovement)
    (rightNumeratorBound : normSq rightNumerator <= numeratorBound)
    (rightDenominatorBound : normSq rightDenominator <= denominatorBound)
    (rootDifference : normSq (rightDenominator - leftDenominator) <=
      rootMovement)
    (leftLower : lowerSq <= normSq leftDenominator)
    (rightLower : lowerSq <= normSq rightDenominator) :
    normSq (leftNumerator / leftDenominator -
        rightNumerator / rightDenominator) <=
      quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
        pointMovement rootMovement := by
  have leftNormPositive : 0 < normSq leftDenominator :=
    lowerPositive.trans_le leftLower
  have rightNormPositive : 0 < normSq rightDenominator :=
    lowerPositive.trans_le rightLower
  have leftNonzero : leftDenominator ≠ 0 := by
    intro zero
    rw [zero, normSq_zero] at leftNormPositive
    exact (lt_irrefl _ leftNormPositive).elim
  have rightNonzero : rightDenominator ≠ 0 := by
    intro zero
    rw [zero, normSq_zero] at rightNormPositive
    exact (lt_irrefl _ rightNormPositive).elim
  have slopeMovementNonnegative :
      0 <= numeratorSlope * pointMovement :=
    (normSq_nonneg (leftNumerator - rightNumerator)).trans
      numeratorDifference
  have numeratorBoundNonnegative : 0 <= numeratorBound :=
    (normSq_nonneg rightNumerator).trans rightNumeratorBound
  have denominatorBoundNonnegative : 0 <= denominatorBound :=
    (normSq_nonneg rightDenominator).trans rightDenominatorBound
  have rootMovementNonnegative : 0 <= rootMovement :=
    (normSq_nonneg (rightDenominator - leftDenominator)).trans
      rootDifference
  have numeratorIdentity :
      leftNumerator * rightDenominator -
          rightNumerator * leftDenominator =
        (leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  have numeratorEstimate :
      normSq (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) <=
        2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement) := by
    rw [numeratorIdentity]
    calc
      normSq ((leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator)) <=
        2 *
          (normSq ((leftNumerator - rightNumerator) * rightDenominator) +
            normSq (rightNumerator *
              (rightDenominator - leftDenominator))) :=
        normSq_add_le_two _ _
      _ = 2 *
          (normSq (leftNumerator - rightNumerator) *
              normSq rightDenominator +
            normSq rightNumerator *
              normSq (rightDenominator - leftDenominator)) := by
        rw [normSq_mul, normSq_mul]
      _ <= 2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement) := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_direct
              numeratorDifference rightDenominatorBound
              (normSq_nonneg rightDenominator)
              slopeMovementNonnegative)
            (RFAP.ConstructiveFraction.mul_le_mul_direct
              rightNumeratorBound rootDifference
              (normSq_nonneg (rightDenominator - leftDenominator))
              numeratorBoundNonnegative)
        · decide
  have denominatorLower : lowerSq * lowerSq <=
      normSq leftDenominator * normSq rightDenominator :=
    RFAP.ConstructiveFraction.mul_le_mul_direct leftLower rightLower
      lowerPositive.le (normSq_nonneg leftDenominator)
  have denominatorPositive :
      0 < normSq leftDenominator * normSq rightDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct leftNormPositive
      rightNormPositive
  rw [div_sub_div leftNumerator rightNumerator leftDenominator
      rightDenominator leftNonzero rightNonzero,
    normSq_div _ _ (mul_ne_zero_direct leftNonzero rightNonzero),
    normSq_mul]
  change
    normSq (leftNumerator * rightDenominator -
        rightNumerator * leftDenominator) /
      (normSq leftDenominator * normSq rightDenominator) <= _
  calc
    normSq (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (normSq leftDenominator * normSq rightDenominator) <=
      (2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement)) /
        (normSq leftDenominator * normSq rightDenominator) := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos
        denominatorPositive).2
      exact numeratorEstimate.trans_eq
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          denominatorPositive.ne').symm
    _ <= (2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement)) / (lowerSq * lowerSq) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (by
          exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                slopeMovementNonnegative denominatorBoundNonnegative)
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                numeratorBoundNonnegative rootMovementNonnegative)))
        (RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive)
        denominatorLower

end CCL.ArithmeticFiniteQuotientVariation

