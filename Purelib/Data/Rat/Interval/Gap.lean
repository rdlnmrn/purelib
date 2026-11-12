module

import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Rational interval gaps

The sign of the retained endpoints determines the distance of a closed rational interval from zero. Its nonnegative gap
bounds the magnitude and square of every contained value.
-/

namespace Purelib.Data.Rat.Interval.Gap

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat

/-- Compute the interval's distance from zero, returning zero when it crosses zero.

For an interval entirely to the right, use its lower endpoint; for one entirely to the left, use the negated upper
endpoint. If neither case applies, return zero, giving a nonnegative lower bound on the magnitude of every contained
value. -/
@[expose] public def gap (interval : Bounds) : Fraction.Rational :=
  if 0 ≤ interval.lower then interval.lower else
    if interval.upper ≤ 0 then -interval.upper else 0

/-- The computed interval gap from zero is nonnegative.

The right-side branch retains a nonnegative lower endpoint. The left-side branch negates a nonpositive upper endpoint,
and the crossing branch retains zero. -/
public theorem gap_nonnegative (interval : Bounds) : 0 ≤ Interval.Gap.gap interval := by
  unfold Interval.Gap.gap
  split
  · assumption
  · split
    · rename_i nonpositive
      simpa only [neg_zero] using Order.Arithmetic.neg_le_neg_direct nonpositive
    · exact le_rfl

/-- The computed interval gap vanishes exactly when the closed interval contains zero.

The endpoint branches include equality, so a retained endpoint at zero is a
collision as well as an interior crossing. -/
public theorem gap_eq_zero_iff (interval : Bounds) :
    gap interval = 0 ↔ interval.Contains 0 := by
  unfold gap
  split
  · rename_i lowerNonnegative
    constructor
    · intro lowerZero
      exact ⟨lowerZero.le, lowerNonnegative.trans interval.valid⟩
    · intro inside
      exact Fraction.Order.Basic.le_antisymm _ _ inside.1 lowerNonnegative
  · rename_i lowerNotNonnegative
    split
    · rename_i upperNonpositive
      constructor
      · intro negativeUpperZero
        have upperZero : interval.upper = 0 := by
          calc
            interval.upper = -(-interval.upper) := (neg_neg _).symm
            _ = -(0 : Fraction.Rational) := congrArg Neg.neg negativeUpperZero
            _ = 0 := neg_zero
        exact ⟨interval.valid.trans_eq upperZero, upperZero.symm.le⟩
      · intro inside
        have upperZero := Fraction.Order.Basic.le_antisymm _ _ upperNonpositive inside.2
        rw [upperZero]
        rfl
    · rename_i upperNotNonpositive
      constructor
      · intro _
        exact ⟨(Order.Arithmetic.lt_of_not_ge_direct lowerNotNonnegative).le,
          (Order.Arithmetic.lt_of_not_ge_direct upperNotNonpositive).le⟩
      · intro _
        rfl

/-- The interval gap is at most the absolute value of every contained rational.

Containment bounds the value by the retained endpoints. In each one-sided branch the corresponding endpoint magnitude is
bounded by the value or its negation. -/
public theorem gap_le_abs (interval : Bounds) {value : Fraction.Rational}
    (inside : interval.Contains value) : gap interval ≤ Fraction.abs value := by
  unfold gap
  split
  · exact inside.1.trans (Fraction.Order.Basic.le_max_left _ _)
  · split
    · exact (Order.Arithmetic.neg_le_neg_direct inside.2).trans
        (Fraction.Order.Basic.le_max_right _ _)
    · exact Order.Arithmetic.abs_nonneg_direct value

/-- The squared interval gap is at most the square of every contained rational.

Both the gap and its magnitude ceiling are nonnegative. Squaring their comparison and identifying the magnitude square
gives the bound on the contained value square. -/
public theorem gap_sq_le (interval : Bounds) {value : Fraction.Rational}
    (inside : interval.Contains value) : gap interval ^ 2 ≤ value ^ 2 := by
  have bound := Order.Arithmetic.pow_le_pow_direct
    (gap_nonnegative interval) (gap_le_abs interval inside) 2
  rw [Bounds.Abs.abs_sq_direct] at bound
  exact bound

/-- Compute the original interval gap from a displayed rational point by translating that point to zero.

The original two interval endpoints receive the same negative point shift.
The existing zero-gap procedure then reads their exact distance from zero,
returning zero precisely when the original interval contains the point. -/
@[expose] public def gapFrom (interval : Bounds) (point : Fraction.Rational) : Fraction.Rational :=
  gap (Arithmetic.addConstant interval (-point))

/-- The original interval gap from every displayed rational point is nonnegative. -/
public theorem gapFrom_nonnegative (interval : Bounds) (point : Fraction.Rational) :
    0 ≤ gapFrom interval point := gap_nonnegative _

/-- Excluding the displayed rational point makes the same computed original interval gap strictly positive. -/
public theorem gapFrom_positive (interval : Bounds) (point : Fraction.Rational)
    (outside : ¬ interval.Contains point) : 0 < gapFrom interval point := by
  have nonzero : gapFrom interval point ≠ 0 := by
    intro zero
    have contained := (gap_eq_zero_iff (Arithmetic.addConstant interval (-point))).mp zero
    have lower := Order.Arithmetic.add_le_add_right_direct contained.1 point
    have upper := Order.Arithmetic.add_le_add_right_direct contained.2 point
    change (interval.lower + -point) + point ≤ 0 + point at lower
    change 0 + point ≤ (interval.upper + -point) + point at upper
    rewrite [show interval.lower + -point + point = interval.lower by ring1,
      show (0 : Fraction.Rational) + point = point by ring1] at lower
    rewrite [show interval.upper + -point + point = interval.upper by ring1,
      show (0 : Fraction.Rational) + point = point by ring1] at upper
    exact outside ⟨lower, upper⟩
  exact ⟨gapFrom_nonnegative interval point,
    fun reverse => nonzero (Fraction.Order.Basic.le_antisymm _ _ reverse (gapFrom_nonnegative interval point))⟩

/-- The original interval gap pays every contained value's displacement magnitude from the same displayed point. -/
public theorem gapFrom_le_abs (interval : Bounds) (point : Fraction.Rational) {value : Fraction.Rational}
    (inside : interval.Contains value) : gapFrom interval point ≤ Fraction.abs (value - point) := by
  have paid := gap_le_abs (Arithmetic.addConstant interval (-point))
    (Arithmetic.addConstant_contains interval (-point) inside)
  rewrite [show value + -point = value - point by ring1] at paid
  exact paid

end Purelib.Data.Rat.Interval.Gap
