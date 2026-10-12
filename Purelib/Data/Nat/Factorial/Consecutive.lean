module
public import Purelib.Data.Nat.Factorial.Basic

import Purelib.Data.Nat.Multiplication

/-!
# Products of consecutive natural factors

The finite product retains its starting value and factor count. Head and tail
recurrences identify the same multiplication procedure with natural factorials.
-/

public section
namespace Purelib.Data.Nat.Factorial.Consecutive

open Purelib.Data.Nat
open Purelib.Data.Nat.Factorial

/-- Multiply a displayed number of consecutive natural factors.

The empty product is one. A successor product multiplies the starting value by the
shorter product starting one higher; a zero starting value is allowed. -/
@[expose] def consecutiveProduct : Nat → Nat → Nat
  | _, 0 => 1
  | denominator, count + 1 =>
      denominator * Purelib.Data.Nat.Factorial.Consecutive.consecutiveProduct (denominator + 1) count

/-- A product of zero consecutive factors is one. -/
@[simp] theorem consecutiveProduct_zero (denominator : Nat) :
    Consecutive.consecutiveProduct denominator 0 = 1 := rfl

/-- Expose the first factor of a nonempty consecutive product. -/
@[simp] theorem consecutiveProduct_succ_head
    (denominator count : Nat) :
    Consecutive.consecutiveProduct denominator (count + 1) =
      denominator * Consecutive.consecutiveProduct (denominator + 1) count := rfl

/-- Expose the last factor of a nonempty consecutive product.

A product of count + 1 factors starting at denominator equals the first count factors
times denominator + count. -/
theorem consecutiveProduct_succ_tail (denominator : Nat) :
    ∀ count : Nat,
      Consecutive.consecutiveProduct denominator (count + 1) =
        Consecutive.consecutiveProduct denominator count * (denominator + count)
  | 0 => by
      change denominator * 1 = 1 * (denominator + 0)
      rw [Nat.add_zero, Nat.mul_one, Nat.one_mul]
  | count + 1 => by
      calc
        Consecutive.consecutiveProduct denominator (count + 1 + 1) =
            denominator *
              Consecutive.consecutiveProduct (denominator + 1) (count + 1) := rfl
        _ = denominator *
            (Consecutive.consecutiveProduct (denominator + 1) count *
              (denominator + 1 + count)) := by
          rw [Purelib.Data.Nat.Factorial.Consecutive.consecutiveProduct_succ_tail (denominator + 1) count]
        _ = Consecutive.consecutiveProduct denominator (count + 1) *
            (denominator + (count + 1)) := by
          rw [Consecutive.consecutiveProduct_succ_head]
          rw [Multiplication.mul_assoc]
          exact congrArg (fun last => denominator *
            (Consecutive.consecutiveProduct (denominator + 1) count * last))
            (by rw [Nat.add_assoc, Nat.one_add])

/-- Consecutive multiplication starting at one computes the factorial.

The last-factor recurrence appends the next positive natural factor to the
same retained finite product, matching the factorial successor equation. -/
theorem consecutiveProduct_one_eq_factorial : ∀ degree : Nat,
    Consecutive.consecutiveProduct 1 degree = Basic.factorial degree
  | 0 => rfl
  | degree + 1 => by
      rw [Consecutive.consecutiveProduct_succ_tail, Basic.factorial_succ,
        Purelib.Data.Nat.Factorial.Consecutive.consecutiveProduct_one_eq_factorial degree]
      congr 1
      exact Nat.one_add degree
end Purelib.Data.Nat.Factorial.Consecutive
end
