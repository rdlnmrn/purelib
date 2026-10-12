module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Constructive finite variation bounds for powers and quotients

These core estimates use only displayed Gaussian rationals and finite induction on
the exponent.  They are the quantitative kernel for constant local models of
`x^k/y` on a prepared hyperelliptic continuation cell.
-/

namespace Purelib.Data.Gaussian.Norm.Quotient.ApproximationQuotientVariation

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Numerator variation, denominator variation and a common positive denominator norm margin bound squared displacement
of the two quotients.

Retain the supplied numerator slope, point movement, root movement, numerator bound and right denominator bound. Both
denominator squared norms meet the same positive lower margin, and the conclusion uses the exact existing quotientBound
expression. -/
theorem normSq_div_sub_div_le
    {leftNumerator rightNumerator leftDenominator rightDenominator : Basic.Canonical}
    {numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Fraction.Rational}
    (lowerPositive : 0 < lowerSq)
    (numeratorDifference :
      Data.Gaussian.Norm.Basic.normSq (leftNumerator - rightNumerator) <=
        numeratorSlope * pointMovement)
    (rightNumeratorBound : Data.Gaussian.Norm.Basic.normSq rightNumerator <= numeratorBound)
    (rightDenominatorBound : Data.Gaussian.Norm.Basic.normSq rightDenominator <= denominatorBound)
    (rootDifference : Data.Gaussian.Norm.Basic.normSq (rightDenominator - leftDenominator) <=
      rootMovement)
    (leftLower : lowerSq <= Data.Gaussian.Norm.Basic.normSq leftDenominator)
    (rightLower : lowerSq <= Data.Gaussian.Norm.Basic.normSq rightDenominator) :
    Data.Gaussian.Norm.Basic.normSq (leftNumerator / leftDenominator -
        rightNumerator / rightDenominator) <=
      Budget.Quotient.quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
        pointMovement rootMovement := by
  have leftNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq leftDenominator :=
    lowerPositive.trans_le leftLower
  have rightNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq rightDenominator :=
    lowerPositive.trans_le rightLower
  have leftNonzero : leftDenominator ≠ 0 := by
    intro zero
    rw [zero, Norm.Basic.normSq_zero] at leftNormPositive
    exact (lt_irrefl _ leftNormPositive).elim
  have rightNonzero : rightDenominator ≠ 0 := by
    intro zero
    rw [zero, Norm.Basic.normSq_zero] at rightNormPositive
    exact (lt_irrefl _ rightNormPositive).elim
  have slopeMovementNonnegative :
      0 <= numeratorSlope * pointMovement :=
    (Norm.Basic.normSq_nonneg (leftNumerator - rightNumerator)).trans
      numeratorDifference
  have numeratorBoundNonnegative : 0 <= numeratorBound :=
    (Norm.Basic.normSq_nonneg rightNumerator).trans rightNumeratorBound
  have denominatorBoundNonnegative : 0 <= denominatorBound :=
    (Norm.Basic.normSq_nonneg rightDenominator).trans rightDenominatorBound
  have rootMovementNonnegative : 0 <= rootMovement :=
    (Norm.Basic.normSq_nonneg (rightDenominator - leftDenominator)).trans
      rootDifference
  have numeratorIdentity :
      leftNumerator * rightDenominator -
          rightNumerator * leftDenominator =
        (leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  have numeratorEstimate :
      Data.Gaussian.Norm.Basic.normSq (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) <=
        2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement) := by
    rw [numeratorIdentity]
    calc
      Data.Gaussian.Norm.Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator)) <=
        2 *
          (Data.Gaussian.Norm.Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator) +
            Data.Gaussian.Norm.Basic.normSq (rightNumerator *
              (rightDenominator - leftDenominator))) :=
        Norm.Bounds.normSq_add_le_two _ _
      _ = 2 *
          (Data.Gaussian.Norm.Basic.normSq (leftNumerator - rightNumerator) *
              Data.Gaussian.Norm.Basic.normSq rightDenominator +
            Data.Gaussian.Norm.Basic.normSq rightNumerator *
              Data.Gaussian.Norm.Basic.normSq (rightDenominator - leftDenominator)) := by
        rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
      _ <= 2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement) := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add
            (Fraction.Order.Arithmetic.mul_le_mul_direct
              numeratorDifference rightDenominatorBound
              (Norm.Basic.normSq_nonneg rightDenominator)
              slopeMovementNonnegative)
            (Fraction.Order.Arithmetic.mul_le_mul_direct
              rightNumeratorBound rootDifference
              (Norm.Basic.normSq_nonneg (rightDenominator - leftDenominator))
              numeratorBoundNonnegative)
        · decide
  have denominatorLower : lowerSq * lowerSq <=
      Data.Gaussian.Norm.Basic.normSq leftDenominator * Data.Gaussian.Norm.Basic.normSq rightDenominator :=
    Fraction.Order.Arithmetic.mul_le_mul_direct leftLower rightLower
      lowerPositive.le (Norm.Basic.normSq_nonneg leftDenominator)
  have denominatorPositive :
      0 < Data.Gaussian.Norm.Basic.normSq leftDenominator * Data.Gaussian.Norm.Basic.normSq rightDenominator :=
    Fraction.Order.Arithmetic.mul_pos_direct leftNormPositive
      rightNormPositive
  rw [Purelib.Data.Gaussian.Field.div_sub_div leftNumerator rightNumerator leftDenominator
      rightDenominator leftNonzero rightNonzero,
    Field.normSq_div _ _ (Field.mul_ne_zero_direct leftNonzero rightNonzero),
    Norm.Basic.normSq_mul]
  change
    Data.Gaussian.Norm.Basic.normSq (leftNumerator * rightDenominator -
        rightNumerator * leftDenominator) /
      (Data.Gaussian.Norm.Basic.normSq leftDenominator * Data.Gaussian.Norm.Basic.normSq rightDenominator) <= _
  calc
    Data.Gaussian.Norm.Basic.normSq (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (Data.Gaussian.Norm.Basic.normSq leftDenominator * Data.Gaussian.Norm.Basic.normSq rightDenominator) <=
      (2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement)) /
        (Data.Gaussian.Norm.Basic.normSq leftDenominator * Data.Gaussian.Norm.Basic.normSq rightDenominator) := by
      apply (Fraction.Order.Field.div_le_iff_pos
        denominatorPositive).2
      exact numeratorEstimate.trans_eq
        (Fraction.Field.div_mul_cancel_of_ne _ _
          denominatorPositive.ne').symm
    _ <= (2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement)) / (lowerSq * lowerSq) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (by
          exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                slopeMovementNonnegative denominatorBoundNonnegative)
              (Fraction.Order.Arithmetic.mul_nonneg_direct
                numeratorBoundNonnegative rootMovementNonnegative)))
        (Fraction.Order.Arithmetic.mul_pos_direct lowerPositive lowerPositive)
        denominatorLower

end Purelib.Data.Gaussian.Norm.Quotient.ApproximationQuotientVariation

end

@[expose] public section

/-!
# Riemann compatibility facade for finite quotient variation

The constructive Gaussian-rational estimates now live in the arithmetic core,
where progressive division can use them without importing the Riemann layer.
These declarations preserve the established Riemann names for downstream
modules without duplicating their proof bodies.
-/

namespace Purelib.Data.Gaussian.Norm.Quotient.IntegrationQuotientVariation

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Numerator variation, denominator variation and a common positive denominator norm margin bound squared displacement
of the two quotients.

Retain the supplied numerator slope, point movement, root movement, numerator bound and right denominator bound. Both
denominator squared norms meet the same positive lower margin, and the conclusion uses the exact existing quotientBound
expression. -/
theorem normSq_div_sub_div_le
    {leftNumerator rightNumerator leftDenominator rightDenominator : Basic.Canonical}
    {numeratorSlope numeratorBound denominatorBound lowerSq pointMovement
      rootMovement : Fraction.Rational}
    (lowerPositive : 0 < lowerSq)
    (numeratorDifference :
      Data.Gaussian.Norm.Basic.normSq (leftNumerator - rightNumerator) <=
        numeratorSlope * pointMovement)
    (rightNumeratorBound : Data.Gaussian.Norm.Basic.normSq rightNumerator <= numeratorBound)
    (rightDenominatorBound : Data.Gaussian.Norm.Basic.normSq rightDenominator <= denominatorBound)
    (rootDifference : Data.Gaussian.Norm.Basic.normSq (rightDenominator - leftDenominator) <=
      rootMovement)
    (leftLower : lowerSq <= Data.Gaussian.Norm.Basic.normSq leftDenominator)
    (rightLower : lowerSq <= Data.Gaussian.Norm.Basic.normSq rightDenominator) :
    Data.Gaussian.Norm.Basic.normSq (leftNumerator / leftDenominator -
        rightNumerator / rightDenominator) <=
      Budget.Quotient.quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
        pointMovement rootMovement :=
  Norm.Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
    lowerPositive numeratorDifference rightNumeratorBound
    rightDenominatorBound rootDifference leftLower rightLower

end Purelib.Data.Gaussian.Norm.Quotient.IntegrationQuotientVariation

end
