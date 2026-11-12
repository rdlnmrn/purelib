module
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Constructive finite variation bounds for powers and quotients

These core estimates use only displayed Gaussian rationals and finite induction on
the exponent.  They are the quantitative kernel for constant local models of
`x^k/y` on a prepared hyperelliptic continuation cell.
-/

namespace Purelib.Approximation.Rational.Budget.Quotient

/-- A fully rational variation majorant for two quotients. -/
def quotientBound (numeratorSlope numeratorBound denominatorBound
  lowerSq
    pointMovement rootMovement : Fraction.Rational) : Fraction.Rational :=
  (2 * (numeratorSlope * pointMovement * denominatorBound +
    numeratorBound * rootMovement)) / (lowerSq * lowerSq)

/-- The quotient variation bound is nonnegative when every displayed magnitude, floor and movement is nonnegative. -/
theorem ApproximationQuotientVariation.quotientBound_nonnegative
    {numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Fraction.Rational}
    (slopeNonnegative : 0 <= numeratorSlope)
    (numeratorNonnegative : 0 <= numeratorBound)
    (denominatorNonnegative : 0 <= denominatorBound)
    (lowerNonnegative : 0 <= lowerSq)
    (pointNonnegative : 0 <= pointMovement)
    (rootNonnegative : 0 <= rootMovement) :
    0 <= quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
      pointMovement rootMovement :=
  Field.div_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct slopeNonnegative
            pointNonnegative) denominatorNonnegative)
        (Arithmetic.mul_nonneg_direct numeratorNonnegative
          rootNonnegative)))
    (Arithmetic.mul_nonneg_direct lowerNonnegative
      lowerNonnegative)
end Purelib.Approximation.Rational.Budget.Quotient

end

@[expose] public section

/-!
# Riemann compatibility facade for finite quotient variation

The constructive Gaussian-rational estimates now live in the arithmetic core,
where progressive division can use them without importing the Riemann layer.
These declarations preserve the established Riemann names for downstream
modules without duplicating their proof bodies.
-/

namespace Purelib.Approximation.Rational.Budget.Quotient

/-- The quotient variation bound is nonnegative when every displayed magnitude, floor and movement is nonnegative. -/
theorem IntegrationQuotientVariation.quotientBound_nonnegative
    {numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Fraction.Rational}
    (slopeNonnegative : 0 <= numeratorSlope)
    (numeratorNonnegative : 0 <= numeratorBound)
    (denominatorNonnegative : 0 <= denominatorBound)
    (lowerNonnegative : 0 <= lowerSq)
    (pointNonnegative : 0 <= pointMovement)
    (rootNonnegative : 0 <= rootMovement) :
    0 <= quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
      pointMovement rootMovement :=
  ApproximationQuotientVariation.quotientBound_nonnegative
    slopeNonnegative numeratorNonnegative denominatorNonnegative
    lowerNonnegative pointNonnegative rootNonnegative

/-- Increasing a positive squared-denominator floor can only decrease the finite quotient-variation bound. -/
theorem quotientBound_antitone_lowerSq
    {numeratorSlope numeratorBound denominatorBound lowerSq higherSq
      pointMovement rootMovement : Fraction.Rational}
    (slopeNonnegative : 0 <= numeratorSlope)
    (numeratorNonnegative : 0 <= numeratorBound)
    (denominatorNonnegative : 0 <= denominatorBound)
    (pointNonnegative : 0 <= pointMovement)
    (rootNonnegative : 0 <= rootMovement)
    (lowerPositive : 0 < lowerSq)
    (order : lowerSq <= higherSq) :
    quotientBound numeratorSlope numeratorBound denominatorBound higherSq
        pointMovement rootMovement <=
      quotientBound numeratorSlope numeratorBound denominatorBound
        lowerSq
        pointMovement rootMovement := by
  have numeratorTotalNonnegative :
      0 <= 2 * (numeratorSlope * pointMovement * denominatorBound +
        numeratorBound * rootMovement) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct slopeNonnegative
            pointNonnegative)
          denominatorNonnegative)
        (Arithmetic.mul_nonneg_direct numeratorNonnegative
          rootNonnegative))
  have squareOrder : lowerSq * lowerSq <= higherSq * higherSq := by
    simpa only [pow_two] using
      (Arithmetic.pow_le_pow_direct lowerPositive.le order 2)
  unfold quotientBound
  exact Field.div_le_div_of_nonneg_left_direct
    numeratorTotalNonnegative
    (Arithmetic.mul_pos_direct lowerPositive lowerPositive)
    squareOrder

/-- The quotient bound plus its strictly positive root-diameter reserve is the two-term linear form used by prepared
subdivision schedulers. -/
theorem quotientBound_add_rootMovement_eq_linear
    (numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Fraction.Rational) :
    quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
          pointMovement rootMovement + rootMovement =
      ((2 * (numeratorSlope * denominatorBound)) /
          (lowerSq * lowerSq)) * pointMovement +
        ((2 * numeratorBound) / (lowerSq * lowerSq) + 1) * rootMovement := by
  unfold quotientBound
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1
end Purelib.Approximation.Rational.Budget.Quotient

end

public section

namespace Purelib.Approximation.Rational.Budget.Quotient

open Purelib.Data.Rat

/-- Increasing nonnegative numerator, denominator and movement ceilings preserves the finite quotient bound.

The positive squared-denominator floor is shared. Every displayed
magnitude and movement remains an explicit finite scalar; the operation
asserts no nonvanishing or variation away from the supplied ceilings.
-/
theorem quotientBound_mono {slope numerator denominator floor point root
    largerNumerator largerDenominator largerPoint largerRoot : Fraction.Rational}
    (slopeNonnegative : 0 ≤ slope) (numeratorNonnegative : 0 ≤ numerator)
    (pointNonnegative : 0 ≤ point) (rootNonnegative : 0 ≤ root) (floorPositive : 0 < floor)
    (numeratorOrder : numerator ≤ largerNumerator) (denominatorOrder : denominator ≤ largerDenominator)
    (pointOrder : point ≤ largerPoint) (rootOrder : root ≤ largerRoot)
    (denominatorNonnegative : 0 ≤ denominator) :
    quotientBound slope numerator denominator floor point root ≤
      quotientBound slope largerNumerator largerDenominator floor largerPoint largerRoot := by
  have slopePoint := Arithmetic.mul_le_mul_of_nonneg_left_direct pointOrder slopeNonnegative
  have first := Arithmetic.mul_le_mul_direct slopePoint denominatorOrder
    denominatorNonnegative (Arithmetic.mul_nonneg_direct slopeNonnegative
      (pointNonnegative.trans pointOrder))
  have second := Arithmetic.mul_le_mul_direct numeratorOrder rootOrder rootNonnegative
    (numeratorNonnegative.trans numeratorOrder)
  have total := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct first second) (by decide : (0 : Fraction.Rational) ≤ 2)
  exact Fraction.Order.Field.divide_mono total
    (Arithmetic.mul_pos_direct floorPositive floorPositive)

end Purelib.Approximation.Rational.Budget.Quotient

end

public section

namespace Purelib.Approximation.Rational.Budget.Quotient

/-- The common sensitivity of two quotient operands with their displayed magnitude bounds and denominator floor. -/
@[expose] def comparisonCoefficient (numeratorBound denominatorBound lowerSq : Fraction.Rational) :
    Fraction.Rational :=
  (2 * (denominatorBound + numeratorBound)) / (lowerSq * lowerSq)

/-- Divide an output tolerance by one plus the sensitivity of the same quotient operands. -/
@[expose] def comparisonTarget (numeratorBound denominatorBound lowerSq target : Fraction.Rational) :
    Fraction.Rational :=
  target / (1 + comparisonCoefficient numeratorBound denominatorBound lowerSq)

/-- Equal movements factor the quotient bound through its same displayed sensitivity coefficient. -/
private theorem equalMovement (numeratorBound denominatorBound lowerSq movement : Fraction.Rational) :
    quotientBound 1 numeratorBound denominatorBound lowerSq movement movement =
      movement * comparisonCoefficient numeratorBound denominatorBound lowerSq := by
  unfold quotientBound comparisonCoefficient
  rw [Algebra.Field.ExplicitField.div_eq_mul_inv, Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- Nonnegative operand magnitudes and a nonnegative denominator floor give a nonnegative quotient sensitivity. -/
theorem comparisonCoefficient_nonnegative {numeratorBound denominatorBound lowerSq : Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numeratorBound) (denominatorNonnegative : 0 ≤ denominatorBound)
    (lowerNonnegative : 0 ≤ lowerSq) :
    0 ≤ comparisonCoefficient numeratorBound denominatorBound lowerSq := by
  have bounded := ApproximationQuotientVariation.quotientBound_nonnegative
    (by decide : (0 : Fraction.Rational) ≤ 1) numeratorNonnegative denominatorNonnegative
    lowerNonnegative (by decide : (0 : Fraction.Rational) ≤ 1) (by decide : (0 : Fraction.Rational) ≤ 1)
  exact bounded.trans_eq ((equalMovement numeratorBound denominatorBound lowerSq 1).trans
    (Fraction.Field.one_mul _))

/-- The unchanged quotient target equals the original allowance at the same retained sensitivity. -/
private theorem comparisonTarget_eq_allowance (numeratorBound denominatorBound lowerSq target : Fraction.Rational) :
    comparisonTarget numeratorBound denominatorBound lowerSq target =
      Weighted.allowance target (comparisonCoefficient numeratorBound denominatorBound lowerSq) :=
  (Weighted.allowance_eq_div_one_add target (comparisonCoefficient numeratorBound denominatorBound lowerSq)).symm

/-- A positive quotient output tolerance gives a positive common operand tolerance. -/
theorem comparisonTarget_positive {numeratorBound denominatorBound lowerSq target : Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numeratorBound) (denominatorNonnegative : 0 ≤ denominatorBound)
    (lowerNonnegative : 0 ≤ lowerSq) (positive : 0 < target) :
    0 < comparisonTarget numeratorBound denominatorBound lowerSq target := by
  rewrite [comparisonTarget_eq_allowance]
  exact Weighted.allowance_positive positive
    (comparisonCoefficient_nonnegative numeratorNonnegative denominatorNonnegative lowerNonnegative)

/-- The common operand target times its sensitivity stays strictly below the original output tolerance. -/
theorem comparisonTarget_budget_lt {numeratorBound denominatorBound lowerSq target : Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numeratorBound) (denominatorNonnegative : 0 ≤ denominatorBound)
    (lowerNonnegative : 0 ≤ lowerSq) (positive : 0 < target) :
    comparisonTarget numeratorBound denominatorBound lowerSq target *
      comparisonCoefficient numeratorBound denominatorBound lowerSq < target := by
  rewrite [comparisonTarget_eq_allowance, Fraction.Field.mul_comm]
  exact Weighted.mul_allowance_lt positive
    (comparisonCoefficient_nonnegative numeratorNonnegative denominatorNonnegative lowerNonnegative)

/-- The common operand target pays the actual quotient bound with those same two operand movements. -/
theorem comparison_budget_lt {numeratorBound denominatorBound lowerSq target : Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numeratorBound) (denominatorNonnegative : 0 ≤ denominatorBound)
    (lowerNonnegative : 0 ≤ lowerSq) (positive : 0 < target) :
    quotientBound 1 numeratorBound denominatorBound lowerSq
      (comparisonTarget numeratorBound denominatorBound lowerSq target)
      (comparisonTarget numeratorBound denominatorBound lowerSq target) < target :=
  (equalMovement numeratorBound denominatorBound lowerSq
    (comparisonTarget numeratorBound denominatorBound lowerSq target)).trans_lt
    (comparisonTarget_budget_lt numeratorNonnegative denominatorNonnegative lowerNonnegative positive)

end Purelib.Approximation.Rational.Budget.Quotient

end
