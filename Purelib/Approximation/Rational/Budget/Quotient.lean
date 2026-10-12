module
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
  Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct slopeNonnegative
            pointNonnegative) denominatorNonnegative)
        (Fraction.Order.Arithmetic.mul_nonneg_direct numeratorNonnegative
          rootNonnegative)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct lowerNonnegative
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
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct slopeNonnegative
            pointNonnegative)
          denominatorNonnegative)
        (Fraction.Order.Arithmetic.mul_nonneg_direct numeratorNonnegative
          rootNonnegative))
  have squareOrder : lowerSq * lowerSq <= higherSq * higherSq := by
    simpa only [pow_two] using
      (Fraction.Order.Arithmetic.pow_le_pow_direct lowerPositive.le order 2)
  unfold quotientBound
  exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    numeratorTotalNonnegative
    (Fraction.Order.Arithmetic.mul_pos_direct lowerPositive lowerPositive)
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
