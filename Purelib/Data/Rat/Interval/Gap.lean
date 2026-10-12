module

import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Rational interval gaps

The sign of the retained endpoints determines the distance of a closed rational interval from zero. Its nonnegative gap
bounds the magnitude and square of every contained value.
-/

namespace Purelib.Data.Rat.Interval.Gap

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
      simpa only [neg_zero] using Fraction.Order.Arithmetic.neg_le_neg_direct nonpositive
    · exact le_rfl

/-- The interval gap is at most the absolute value of every contained rational.

Containment bounds the value by the retained endpoints. In each one-sided branch the corresponding endpoint magnitude is
bounded by the value or its negation. -/
public theorem gap_le_abs (interval : Bounds) {value : Fraction.Rational}
    (inside : interval.Contains value) : gap interval ≤ Fraction.abs value := by
  unfold gap
  split
  · exact inside.1.trans (Fraction.Order.Basic.le_max_left _ _)
  · split
    · exact (Fraction.Order.Arithmetic.neg_le_neg_direct inside.2).trans
        (Fraction.Order.Basic.le_max_right _ _)
    · exact Fraction.Order.Arithmetic.abs_nonneg_direct value

/-- The squared interval gap is at most the square of every contained rational.

Both the gap and its magnitude ceiling are nonnegative. Squaring their comparison and identifying the magnitude square
gives the bound on the contained value square. -/
public theorem gap_sq_le (interval : Bounds) {value : Fraction.Rational}
    (inside : interval.Contains value) : gap interval ^ 2 ≤ value ^ 2 := by
  have bound := Fraction.Order.Arithmetic.pow_le_pow_direct
    (gap_nonnegative interval) (gap_le_abs interval inside) 2
  rw [Bounds.Abs.abs_sq_direct] at bound
  exact bound

end Purelib.Data.Rat.Interval.Gap
