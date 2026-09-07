import CCL.Arithmetic.FiniteQuotientVariation

/-!
# Riemann compatibility facade for finite quotient variation

The constructive Gaussian-rational estimates now live in the arithmetic core,
where progressive division can use them without importing the Riemann layer.
These declarations preserve the established Riemann names for downstream
modules without duplicating their proof bodies.
-/

namespace CCL.Riemann.FiniteQuotientVariation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

abbrev powerSlope (radiusSq : Coordinate) (exponent : Nat) : Coordinate :=
  CCL.ArithmeticFiniteQuotientVariation.powerSlope radiusSq exponent

theorem powerSlope_nonnegative {radiusSq : Coordinate}
    (radiusNonnegative : 0 <= radiusSq) (exponent : Nat) :
    0 <= powerSlope radiusSq exponent :=
  CCL.ArithmeticFiniteQuotientVariation.powerSlope_nonnegative
    radiusNonnegative exponent

theorem normSq_pow_sub_pow_le {radiusSq : Coordinate}
    (radiusNonnegative : 0 <= radiusSq) (exponent : Nat)
    {left right : Gaussian} (leftBound : normSq left <= radiusSq)
    (rightBound : normSq right <= radiusSq) :
    normSq (left ^ exponent - right ^ exponent) <=
      powerSlope radiusSq exponent * normSq (left - right) :=
  CCL.ArithmeticFiniteQuotientVariation.normSq_pow_sub_pow_le
    radiusNonnegative exponent leftBound rightBound

theorem div_sub_div (leftNumerator rightNumerator leftDenominator
    rightDenominator : Gaussian)
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0) :
    leftNumerator / leftDenominator -
        rightNumerator / rightDenominator =
      (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (leftDenominator * rightDenominator) :=
  CCL.ArithmeticFiniteQuotientVariation.div_sub_div
    leftNumerator rightNumerator leftDenominator rightDenominator
    leftNonzero rightNonzero

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
  CCL.ArithmeticFiniteQuotientVariation.quotientBound_nonnegative
    slopeNonnegative numeratorNonnegative denominatorNonnegative
    lowerNonnegative pointNonnegative rootNonnegative

/-- Increasing a positive squared-denominator floor can only decrease the
finite quotient-variation bound. -/
theorem quotientBound_antitone_lowerSq
    {numeratorSlope numeratorBound denominatorBound lowerSq higherSq
      pointMovement rootMovement : Coordinate}
    (slopeNonnegative : 0 <= numeratorSlope)
    (numeratorNonnegative : 0 <= numeratorBound)
    (denominatorNonnegative : 0 <= denominatorBound)
    (pointNonnegative : 0 <= pointMovement)
    (rootNonnegative : 0 <= rootMovement)
    (lowerPositive : 0 < lowerSq)
    (order : lowerSq <= higherSq) :
    quotientBound numeratorSlope numeratorBound denominatorBound higherSq
        pointMovement rootMovement <=
      quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
        pointMovement rootMovement := by
  have numeratorTotalNonnegative :
      0 <= 2 * (numeratorSlope * pointMovement * denominatorBound +
        numeratorBound * rootMovement) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct slopeNonnegative
            pointNonnegative)
          denominatorNonnegative)
        (RFAP.ConstructiveFraction.mul_nonneg_direct numeratorNonnegative
          rootNonnegative))
  have squareOrder : lowerSq * lowerSq <= higherSq * higherSq := by
    simpa only [pow_two] using
      (RFAP.ConstructiveFraction.pow_le_pow_direct lowerPositive.le order 2)
  unfold quotientBound
  exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
    numeratorTotalNonnegative
    (RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive)
    squareOrder

/-- The quotient bound plus its strictly positive root-diameter reserve is
the two-term linear form used by prepared subdivision schedulers. -/
theorem quotientBound_add_rootMovement_eq_linear
    (numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Coordinate) :
    quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
          pointMovement rootMovement + rootMovement =
      ((2 * (numeratorSlope * denominatorBound)) /
          (lowerSq * lowerSq)) * pointMovement +
        ((2 * numeratorBound) / (lowerSq * lowerSq) + 1) * rootMovement := by
  unfold quotientBound
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- A small reusable arithmetic kernel for owner-specific denominator
improvements in the two linear quotient coefficients. -/
theorem scaled_div_square_antitone
    {numerator lower higher : Coordinate}
    (numeratorNonnegative : 0 <= numerator)
    (lowerPositive : 0 < lower) (order : lower <= higher) :
    numerator / (higher * higher) <= numerator / (lower * lower) := by
  have squareOrder : lower * lower <= higher * higher := by
    simpa only [pow_two] using
      (RFAP.ConstructiveFraction.pow_le_pow_direct lowerPositive.le order 2)
  exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
    numeratorNonnegative
    (RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive)
    squareOrder

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
        pointMovement rootMovement :=
  CCL.ArithmeticFiniteQuotientVariation.normSq_div_sub_div_le
    lowerPositive numeratorDifference rightNumeratorBound
    rightDenominatorBound rootDifference leftLower rightLower

end CCL.Riemann.FiniteQuotientVariation
