module

public import Init.Data.Nat.Basic
import Purelib.Data.Nat.Subtraction

namespace Purelib.Data.Nat.Multiplication

/-- The square of a natural value is its self-product.

The original natural power procedure takes two finite multiplication steps.
Removing the initial unit factor retains the same two occurrences of the
supplied natural value without generic ring normalization. -/
public theorem pow_two (value : Nat) : value ^ 2 = value * value := by
  change (1 * value) * value = value * value
  rewrite [Nat.one_mul]
  exact Eq.refl _

/-- Natural multiplication distributes over a sum in the right factor. -/
public theorem left_distrib (left first second : Nat) :
    left * (first + second) = left * first + left * second := by
  induction second with
  | zero => rfl
  | succ second ih =>
      rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, Nat.add_assoc]

/-- Natural multiplication distributes over a sum in the left factor. -/
public theorem right_distrib (first second right : Nat) :
    (first + second) * right = first * right + second * right := by
  rw [Nat.mul_comm (first + second) right, left_distrib,
    Nat.mul_comm right first, Nat.mul_comm right second]

/-- Regrouping three natural factors preserves their product. -/
public theorem mul_assoc (first second third : Nat) :
    first * second * third = first * (second * third) := by
  induction third with
  | zero => rfl
  | succ third ih =>
      rw [Nat.mul_succ, Nat.mul_succ, left_distrib, ih]

/-- Multiplying a natural predecessor subtracts one copy of the right factor. -/
private theorem pred_mul (left right : Nat) :
    left.pred * right = left * right - right := by
  cases left with
  | zero => rw [Nat.pred_zero, Nat.zero_mul, Nat.zero_sub]
  | succ left =>
      rw [Nat.pred_succ, Nat.succ_mul, Nat.add_comm (left * right) right,
        Subtraction.add_sub_cancel_left]

/-- Natural multiplication distributes over truncated subtraction in the left factor.

Subtracting the right-scaled subtrahend gives the same truncated natural
difference as scaling the original difference. -/
public theorem right_sub_distrib (first second right : Nat) :
    (first - second) * right = first * right - second * right := by
  induction second with
  | zero => rw [Nat.sub_zero, Nat.zero_mul, Nat.sub_zero]
  | succ second ih =>
      rw [Nat.sub_succ, pred_mul, ih, Nat.succ_mul, Subtraction.sub_sub]

/-- Natural multiplication distributes over truncated subtraction in the right factor.

The same left factor scales both terms of the displayed natural difference,
including differences that truncate to zero. -/
public theorem left_sub_distrib (left first second : Nat) :
    left * (first - second) = left * first - left * second := by
  rw [Nat.mul_comm left (first - second), right_sub_distrib,
    Nat.mul_comm first left, Nat.mul_comm second left]

end Purelib.Data.Nat.Multiplication
