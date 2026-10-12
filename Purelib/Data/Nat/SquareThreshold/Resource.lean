module

public import Purelib.Data.Nat.SquareThreshold.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Nat.Basic

/-!
# Square-threshold resource bounds

The bounded square scan retains its comparison budget and brackets the
selected threshold by the failed square comparison at its predecessor.
-/

open Purelib.Data

public section

namespace Purelib.Data.Nat.SquareThreshold.Resource

/-- The bounded square scan uses at most `input + 1` comparison-bearing recursive
clauses. -/
@[expose] def squareThresholdComparisonBudget (input : Nat) : Nat := input + 1

/-- Exact comparison budget used by `squareThreshold`. -/
theorem squareThreshold_fuel_eq_budget (input : Nat) :
    input + 1 = squareThresholdComparisonBudget input := rfl

/-- The selected threshold is no larger than the elementary working candidate `input +
1`. -/
theorem squareThreshold_le_add_one (input : Nat) :
    Basic.squareThreshold input ≤ input + 1 := by
  apply Basic.squareThreshold_minimal
    (Nat.zero_lt_succ input)
  have oneLe : 1 ≤ input + 1 := Nat.succ_le_succ (Nat.zero_le input)
  have multiplied := Nat.mul_le_mul_left (input + 1) oneLe
  calc
    input < input + 1 := Nat.lt_succ_self input
    _ = (input + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (input + 1) * (input + 1) := multiplied

/-- The successful square threshold is bracketed by the failure of its predecessor. -/
theorem squareThreshold_predecessor_sq_le (input : Nat) :
    (Basic.squareThreshold input - 1) *
        (Basic.squareThreshold input - 1) ≤ input := by
  let output := Basic.squareThreshold input
  by_cases outputOne : output = 1
  · change (output - 1) * (output - 1) ≤ input
    rewrite [outputOne]
    exact Nat.zero_le input
  · have outputPositive := Basic.squareThreshold_pos input
    have oneLtOutput : 1 < output :=
      Nat.lt_of_le_of_ne outputPositive (Ne.symm outputOne)
    have predecessorPositive : 0 < output - 1 :=
      Nat.Subtraction.sub_pos_of_lt oneLtOutput
    apply le_of_not_gt
    intro predecessorWorks
    have minimal := Basic.squareThreshold_minimal
      predecessorPositive predecessorWorks
    dsimp only [output] at minimal
    exact (Nat.not_lt_of_ge minimal)
      (Nat.sub_lt outputPositive (by decide))

end Purelib.Data.Nat.SquareThreshold.Resource
