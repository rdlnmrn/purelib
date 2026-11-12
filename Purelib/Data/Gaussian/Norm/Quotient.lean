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

open Purelib.Data.Rat.Fraction.Order

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
      Basic.normSq (leftNumerator - rightNumerator) <=
        numeratorSlope * pointMovement)
    (rightNumeratorBound : Basic.normSq rightNumerator <= numeratorBound)
    (rightDenominatorBound : Basic.normSq rightDenominator <= denominatorBound)
    (rootDifference : Basic.normSq (rightDenominator - leftDenominator) <=
      rootMovement)
    (leftLower : lowerSq <= Basic.normSq leftDenominator)
    (rightLower : lowerSq <= Basic.normSq rightDenominator) :
    Basic.normSq (leftNumerator / leftDenominator -
        rightNumerator / rightDenominator) <=
      Budget.Quotient.quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
        pointMovement rootMovement := by
  have leftNormPositive : 0 < Basic.normSq leftDenominator :=
    lowerPositive.trans_le leftLower
  have rightNormPositive : 0 < Basic.normSq rightDenominator :=
    lowerPositive.trans_le rightLower
  have leftNonzero : leftDenominator ≠ 0 := by
    intro zero
    rw [zero, Basic.normSq_zero] at leftNormPositive
    exact (lt_irrefl _ leftNormPositive).elim
  have rightNonzero : rightDenominator ≠ 0 := by
    intro zero
    rw [zero, Basic.normSq_zero] at rightNormPositive
    exact (lt_irrefl _ rightNormPositive).elim
  have slopeMovementNonnegative :
      0 <= numeratorSlope * pointMovement :=
    (Basic.normSq_nonneg (leftNumerator - rightNumerator)).trans
      numeratorDifference
  have numeratorBoundNonnegative : 0 <= numeratorBound :=
    (Basic.normSq_nonneg rightNumerator).trans rightNumeratorBound
  have denominatorBoundNonnegative : 0 <= denominatorBound :=
    (Basic.normSq_nonneg rightDenominator).trans rightDenominatorBound
  have rootMovementNonnegative : 0 <= rootMovement :=
    (Basic.normSq_nonneg (rightDenominator - leftDenominator)).trans
      rootDifference
  have numeratorIdentity :
      leftNumerator * rightDenominator -
          rightNumerator * leftDenominator =
        (leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  have numeratorEstimate :
      Basic.normSq (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) <=
        2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement) := by
    rw [numeratorIdentity]
    calc
      Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator +
          rightNumerator * (rightDenominator - leftDenominator)) <=
        2 *
          (Basic.normSq ((leftNumerator - rightNumerator) * rightDenominator) +
            Basic.normSq (rightNumerator *
              (rightDenominator - leftDenominator))) :=
        Bounds.normSq_add_le_two _ _
      _ = 2 *
          (Basic.normSq (leftNumerator - rightNumerator) *
              Basic.normSq rightDenominator +
            Basic.normSq rightNumerator *
              Basic.normSq (rightDenominator - leftDenominator)) := by
        rw [Basic.normSq_mul, Basic.normSq_mul]
      _ <= 2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement) := by
        apply Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add
            (Arithmetic.mul_le_mul_direct
              numeratorDifference rightDenominatorBound
              (Basic.normSq_nonneg rightDenominator)
              slopeMovementNonnegative)
            (Arithmetic.mul_le_mul_direct
              rightNumeratorBound rootDifference
              (Basic.normSq_nonneg (rightDenominator - leftDenominator))
              numeratorBoundNonnegative)
        · decide
  have denominatorLower : lowerSq * lowerSq <=
      Basic.normSq leftDenominator * Basic.normSq rightDenominator :=
    Arithmetic.mul_le_mul_direct leftLower rightLower
      lowerPositive.le (Basic.normSq_nonneg leftDenominator)
  have denominatorPositive :
      0 < Basic.normSq leftDenominator * Basic.normSq rightDenominator :=
    Arithmetic.mul_pos_direct leftNormPositive
      rightNormPositive
  rw [Field.div_sub_div leftNumerator rightNumerator leftDenominator
      rightDenominator leftNonzero rightNonzero,
    Field.normSq_div _ _ (Field.mul_ne_zero_direct leftNonzero rightNonzero),
    Basic.normSq_mul]
  change
    Basic.normSq (leftNumerator * rightDenominator -
        rightNumerator * leftDenominator) /
      (Basic.normSq leftDenominator * Basic.normSq rightDenominator) <= _
  calc
    Basic.normSq (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (Basic.normSq leftDenominator * Basic.normSq rightDenominator) <=
      (2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement)) /
        (Basic.normSq leftDenominator * Basic.normSq rightDenominator) := by
      apply (Field.div_le_iff_pos
        denominatorPositive).2
      exact numeratorEstimate.trans_eq
        (Fraction.Field.div_mul_cancel_of_ne _ _
          denominatorPositive.ne').symm
    _ <= (2 * (numeratorSlope * pointMovement * denominatorBound +
          numeratorBound * rootMovement)) / (lowerSq * lowerSq) :=
      Field.div_le_div_of_nonneg_left_direct
        (by
          exact Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Arithmetic.mul_nonneg_direct
                slopeMovementNonnegative denominatorBoundNonnegative)
              (Arithmetic.mul_nonneg_direct
                numeratorBoundNonnegative rootMovementNonnegative)))
        (Arithmetic.mul_pos_direct lowerPositive lowerPositive)
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
      Basic.normSq (leftNumerator - rightNumerator) <=
        numeratorSlope * pointMovement)
    (rightNumeratorBound : Basic.normSq rightNumerator <= numeratorBound)
    (rightDenominatorBound : Basic.normSq rightDenominator <= denominatorBound)
    (rootDifference : Basic.normSq (rightDenominator - leftDenominator) <=
      rootMovement)
    (leftLower : lowerSq <= Basic.normSq leftDenominator)
    (rightLower : lowerSq <= Basic.normSq rightDenominator) :
    Basic.normSq (leftNumerator / leftDenominator -
        rightNumerator / rightDenominator) <=
      Budget.Quotient.quotientBound numeratorSlope numeratorBound denominatorBound lowerSq
        pointMovement rootMovement :=
  ApproximationQuotientVariation.normSq_div_sub_div_le
    lowerPositive numeratorDifference rightNumeratorBound
    rightDenominatorBound rootDifference leftLower rightLower

end Purelib.Data.Gaussian.Norm.Quotient.IntegrationQuotientVariation

end
