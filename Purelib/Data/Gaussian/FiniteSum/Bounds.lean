module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

section
public section

/-!
# Recursive norm weights for finite Gaussian sums

Each displayed prefix sum is bounded by its retained term ceiling and the
original natural weight recursion.
-/

namespace Purelib.Data.Gaussian.FiniteSum.Bounds

open Purelib.Algebra

/-- Compute the recursive squared-norm weight for a finite Gaussian sum.

Start from zero and replace each weight by twice its successor. The exact identity weight plus two equals two to the
successor count explains the finite growth used in uniform sum bounds. -/
@[expose] def sumWeight : Nat → Nat
  | 0 => 0
  | count + 1 => 2 * (Purelib.Data.Gaussian.FiniteSum.Bounds.sumWeight count + 1)

section
open Purelib.Data.Gaussian
/-- The empty-sum norm weight is zero. -/
@[simp] theorem sumWeight_zero : FiniteSum.Bounds.sumWeight 0 = 0 := rfl

/-- The successor norm weight is twice the previous weight plus two. -/
@[simp] theorem sumWeight_succ (count : Nat) :
    FiniteSum.Bounds.sumWeight (count + 1) = 2 * (FiniteSum.Bounds.sumWeight count + 1) := rfl

/-- Adding two to the norm weight gives two raised to the successor count. -/
theorem sumWeight_add_two : ∀ count : Nat,
    FiniteSum.Bounds.sumWeight count + 2 = 2 ^ (count + 1)
  | 0 => by decide
  | count + 1 => by
      calc
        FiniteSum.Bounds.sumWeight (count + 1) + 2 =
            2 * (FiniteSum.Bounds.sumWeight count + 1) + 2 := rfl
        _ = 2 * (FiniteSum.Bounds.sumWeight count + 2) := by ring1
        _ = 2 * 2 ^ (count + 1) := by rw [Purelib.Data.Gaussian.FiniteSum.Bounds.sumWeight_add_two count]
        _ = 2 ^ (count + 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ (count + 1 + 1) := (pow_succ 2 (count + 1)).symm

/-- The norm weight is at most two raised to the successor count. -/
theorem sumWeight_le_two_pow (count : Nat) :
    FiniteSum.Bounds.sumWeight count ≤ 2 ^ (count + 1) := by
  rw [← FiniteSum.Bounds.sumWeight_add_two count]
  exact Nat.le_add_right _ _

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A uniform nonnegative bound on finite Gaussian term norms bounds the sum norm by the corresponding recursive weight.

The bound applies to each index strictly below the retained count. Induction over the original prefix sum combines the
previous bound with the final term through the squared-norm addition inequality. -/
theorem sum_uniform_normSq_le (term : Nat → Basic.Canonical) :
    ∀ (count : Nat) (bound : Fraction.Rational), 0 ≤ bound →
      (∀ index, index < count → Norm.Basic.normSq (term index) ≤ bound) →
      Norm.Basic.normSq (FiniteSum.Prefix.sum term count) ≤
        (FiniteSum.Bounds.sumWeight count : Fraction.Rational) * bound
  | 0, bound, boundNonnegative, termBound => by
      rw [FiniteSum.Prefix.sum_zero, Norm.Basic.normSq_zero, FiniteSum.Bounds.sumWeight_zero, Nat.cast_zero,
        Fraction.Field.zero_mul_direct]
  | count + 1, bound, boundNonnegative, termBound => by
      rw [FiniteSum.Prefix.sum_succ]
      have prefixBound := Purelib.Data.Gaussian.FiniteSum.Bounds.sum_uniform_normSq_le term count bound
        boundNonnegative (fun index order =>
          termBound index (order.trans (Nat.lt_succ_self count)))
      have finalBound := termBound count (Nat.lt_succ_self count)
      calc
        Norm.Basic.normSq (FiniteSum.Prefix.sum term count + term count) ≤
            2 * (Norm.Basic.normSq (FiniteSum.Prefix.sum term count) + Norm.Basic.normSq (term count))
              :=
          Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * ((FiniteSum.Bounds.sumWeight count : Fraction.Rational) * bound + bound) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add prefixBound finalBound) (by decide)
        _ = (FiniteSum.Bounds.sumWeight (count + 1) : Fraction.Rational) * bound := by
          rw [FiniteSum.Bounds.sumWeight_succ, NatCast.mul, NatCast.add, Nat.cast_ofNat,
            Nat.cast_one]
          ring1
end Purelib.Data.Gaussian.FiniteSum.Bounds

end
