module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Generated sample certificates for the horizontal quartic connector

This module connects the untrusted generated rational root data to the exact
prepared edges cached by the A-forward construction.  The common helpers keep
the proof cost linear in the 64 nonstationary horizontal edges.
-/

namespace Purelib.Data.Rat.Fraction.Order.CrossMultiply

open Purelib.Data.Rat in
/-- For positive denominators, a weak comparison of cross-products gives the corresponding quotient comparison. -/
public theorem horizontalDivLeDivOfCrossMul
    {leftNumerator leftDenominator rightNumerator rightDenominator : Fraction.Rational}
    (leftPositive : 0 < leftDenominator)
    (rightPositive : 0 < rightDenominator)
    (cross : leftNumerator * rightDenominator <=
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator <=
      rightNumerator / rightDenominator := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := leftDenominator * rightDenominator) _
    (Fraction.Order.Arithmetic.mul_pos_direct leftPositive rightPositive)
  calc
    leftNumerator / leftDenominator *
        (leftDenominator * rightDenominator) =
      (leftNumerator / leftDenominator * leftDenominator) *
        rightDenominator := by ring1
    _ = leftNumerator * rightDenominator := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        leftPositive.ne']
    _ <= rightNumerator * leftDenominator := cross
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        rightPositive.ne']
    _ = rightNumerator / rightDenominator *
        (leftDenominator * rightDenominator) := by ring1

end Purelib.Data.Rat.Fraction.Order.CrossMultiply

end
