module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Append

/-!
# Finite squared-norm sums and prefix bounds

These are inequalities on displayed lists only. A bound for a complete
finite word controls all its prefixes without new numerical requests.
-/

public section

namespace Purelib.Data.Gaussian.Basic.Canonical.Norm.Sum.Prefix

open Purelib.Data.List

section
open Purelib.Data.Gaussian
/-- The sum of Gaussian list-entry squared norms is nonnegative. -/
theorem nonnegative (values : List Basic.Canonical) : 0 ≤
  Norm.Sum.Basic.gaussianNormSqSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values ih => exact add_nonneg (Basic.Canonical.normSq_nonneg value) ih

/-- Appending Gaussian lists adds their retained squared-norm sums. -/
theorem append (first last : List Basic.Canonical) :
    Norm.Sum.Basic.gaussianNormSqSum (first ++ last) = Norm.Sum.Basic.gaussianNormSqSum first +
      Norm.Sum.Basic.gaussianNormSqSum last := by
  induction first with
  | nil => change Norm.Sum.Basic.gaussianNormSqSum last = 0 + Norm.Sum.Basic.gaussianNormSqSum last; ring1
  | cons value values ih => simp only [List.cons_append, Norm.Sum.Basic.gaussianNormSqSum, ih]; ring1

end

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A prefix squared-norm sum is at most the corresponding sum after appending the retained suffix. -/
theorem prefix_le (first last : List Basic.Canonical) :
  Norm.Sum.Basic.gaussianNormSqSum first ≤ Norm.Sum.Basic.gaussianNormSqSum (first ++ last) := by
  rw [append]
  have estimate :=
    Fraction.Order.Arithmetic.add_le_add_right_direct (nonnegative last)
      (Norm.Sum.Basic.gaussianNormSqSum first)
  rw [Fraction.Field.zero_add,
    Fraction.Field.add_comm
      (Norm.Sum.Basic.gaussianNormSqSum last)
      (Norm.Sum.Basic.gaussianNormSqSum first)] at estimate
  exact estimate

/-- The prefix Gaussian-sum norm is bounded by total list length times the total squared-norm sum.

The retained suffix increases the displayed count and squared-norm sum. These two nonnegative bounds control the same
original prefix sum. -/
theorem prefix_sum_le (first last : List Basic.Canonical) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum first) ≤ ((first ++ last).length : Fraction.Rational) *
      Norm.Sum.Basic.gaussianNormSqSum (first ++ last) := by
  have count : first.length ≤ (first ++ last).length := by rw [Append.length_append]; exact Nat.le_add_right _ _
  simpa only [Norm.Basic.normSq_eq_canonical] using
    (Norm.Sum.Basic.normSq_gaussianSum_le first).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (prefix_le first last)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Cast.Order.natCast_le_direct count) (nonnegative _)))

end Purelib.Data.Gaussian.Basic.Canonical.Norm.Sum.Prefix
