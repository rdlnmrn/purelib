module

public import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Nat.Subtraction

namespace Purelib.Algebra.NatCast

open Purelib.Data.Nat

/-- Casting a natural sum preserves its two displayed summands. -/
public theorem add {R : Type*} [AddMonoidWithOne R] (left right : Nat) :
    ((left + right : Nat) : R) = (left : R) + (right : R) := by
  induction right with
  | zero => rw [Nat.add_zero, Nat.cast_zero, add_zero]
  | succ right ih =>
      rw [Nat.add_succ, Nat.cast_succ, ih, Nat.cast_succ, add_assoc]

/-- Casting a natural product preserves its two displayed factors. -/
public theorem mul {R : Type*} [Semiring R] (left right : Nat) :
    ((left * right : Nat) : R) = (left : R) * (right : R) := by
  induction right with
  | zero => rw [Nat.mul_zero, Nat.cast_zero, mul_zero]
  | succ right ih =>
      rw [Nat.mul_succ, add, ih, Nat.cast_succ, mul_add, mul_one]

/-- Casting a natural power preserves its base and exponent. -/
public theorem pow {R : Type*} [Semiring R] (value exponent : Nat) :
    ((value ^ exponent : Nat) : R) = (value : R) ^ exponent := by
  induction exponent with
  | zero => rw [Nat.pow_zero, Nat.cast_one, pow_zero]
  | succ exponent ih => rw [Nat.pow_succ, mul, ih, pow_succ]

/-- Casting a bounded natural subtraction preserves the displayed difference.

The retained bound ensures that natural subtraction does not truncate. Casting
its reconstruction equation and canceling the same subtrahend gives the ring
subtraction, with the displayed natural cast and scalar operations.
-/
public theorem sub {R : Type*} [Ring R] {left right : Nat} (bounded : right ≤ left) :
    ((left - right : Nat) : R) = (left : R) - (right : R) := by
  have reconstructed := congrArg (fun value : Nat => (value : R))
    (Subtraction.add_sub_of_le bounded)
  rw [add] at reconstructed
  calc
    ((left - right : Nat) : R) =
        ((right : R) + ((left - right : Nat) : R)) - (right : R) := by
      rw [sub_eq_add_neg, add_comm (right : R) ((left - right : Nat) : R),
        add_assoc, add_neg_cancel, add_zero]
    _ = (left : R) - (right : R) :=
      congrArg (fun value : R => value - (right : R)) reconstructed

end Purelib.Algebra.NatCast
