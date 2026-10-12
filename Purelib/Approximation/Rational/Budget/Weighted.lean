module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Nested finite accuracy budgets for primitive comparisons

Choose a polynomial first.  Its Taylor constant is then a fixed finite
number, however large.  This module selects root tolerance and spatial depth
after that choice, including an arbitrary computed preparation-depth floor.
There is no refinement-uniform Taylor bound or successful-search assumption.
-/

namespace Purelib.Approximation.Rational.Budget.Weighted

/-- A positive tolerance whose weighted cost is at most the request, even when the weight is zero. -/
def allowance (target weight : Fraction.Rational) :
  Fraction.Rational := target / (weight + 1)

/-- A positive target and nonnegative weight give a positive allowance.

Adding one to the retained nonnegative weight gives the original strictly
positive denominator. Division preserves the supplied target's positivity. -/
theorem allowance_positive {target weight : Fraction.Rational}
  (targetPositive : 0 < target)
    (weightNonnegative : 0 ≤ weight) : 0 < allowance target weight :=
  Fraction.Order.Field.div_pos_direct targetPositive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct weightNonnegative (by decide))

/-- For nonnegative target and weight, the weighted allowance does not exceed the target.

The original weight is bounded by its incremented positive denominator.
Multiplication by the retained nonnegative allowance and exact division
cancellation pay the same target, including when the weight is zero. -/
theorem mul_allowance_le {target weight : Fraction.Rational}
  (targetNonnegative : 0 ≤ target)
    (weightNonnegative : 0 ≤ weight) : weight * allowance target weight ≤ target
      := by
  have denominatorPositive : 0 < weight + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    weightNonnegative (by decide)
  have enlarged : weight ≤ weight + 1 := by
    calc
      weight = weight + 0 := (_root_.add_zero weight).symm
      _ ≤ weight + 1 := Fraction.Order.Arithmetic.add_le_add_direct le_rfl (by decide)
  calc
    _ ≤ (weight + 1) * allowance target weight :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        enlarged
        (Fraction.Order.Field.div_nonneg_direct targetNonnegative denominatorPositive.le)
    _ = target := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'

end Purelib.Approximation.Rational.Budget.Weighted

end
