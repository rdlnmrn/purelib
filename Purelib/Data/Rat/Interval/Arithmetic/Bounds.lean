module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

namespace Purelib.Data.Rat.Interval.Arithmetic.Bounds

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds

/-- The square bound of an interval hull is at most the larger input square bound.

The retained hull chooses its endpoints from the two input intervals.
Each chosen endpoint square lies below the maximum of their original
square bounds. -/
public theorem hull_squareBound_le (left right : Bounds) :
    (Interval.Arithmetic.hull left right).squareBound ≤ max left.squareBound right.squareBound := by
  rewrite [Interval.Bounds.squareBound_eq (Interval.Arithmetic.hull left right)]
  apply Order.Basic.max_le
  · exact Square.min_sq_le
      ((left.sq_le_squareBound ⟨Order.Basic.le_refl _, left.valid⟩).trans (Order.Basic.le_max_left _ _))
      ((right.sq_le_squareBound ⟨Order.Basic.le_refl _, right.valid⟩).trans (Order.Basic.le_max_right _ _))
  · exact Square.max_sq_le
      ((left.sq_le_squareBound ⟨left.valid, Order.Basic.le_refl _⟩).trans (Order.Basic.le_max_left _ _))
      ((right.sq_le_squareBound ⟨right.valid, Order.Basic.le_refl _⟩).trans (Order.Basic.le_max_right _ _))

/-- Scaling an interval bounds its endpoint squares by the scalar square times the original square bound.

Both original endpoint products have square bounded by the factor
square times the retained interval square bound. Minimum and maximum
select those same endpoint products. -/
public theorem scale_squareBound_le (factor : Fraction.Rational) (interval : Bounds) :
    (Interval.Arithmetic.scale factor interval).squareBound ≤ factor ^ 2 * interval.squareBound := by
  rewrite [Interval.Bounds.squareBound_eq]
  have lowerBound : (factor * interval.lower) ^ 2 ≤ factor ^ 2 * interval.squareBound := by
    calc
      _ = factor ^ 2 * interval.lower ^ 2 := by ring1
      _ ≤ _ := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by rewrite [Interval.Bounds.squareBound_eq]; exact Order.Basic.le_max_left _ _)
        (Order.Arithmetic.sq_nonneg_direct factor)
  have upperBound : (factor * interval.upper) ^ 2 ≤ factor ^ 2 * interval.squareBound := by
    calc
      _ = factor ^ 2 * interval.upper ^ 2 := by ring1
      _ ≤ _ := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by rewrite [Interval.Bounds.squareBound_eq]; exact Order.Basic.le_max_right _ _)
        (Order.Arithmetic.sq_nonneg_direct factor)
  exact Order.Basic.max_le (Square.min_sq_le lowerBound upperBound)
    (Square.max_sq_le lowerBound upperBound)

/-- The square bound of an interval product is at most the product of the input square bounds.

The original product is the hull of the right interval scaled by each
left endpoint. Each retained endpoint square bounds the corresponding
scaled square bound. -/
public theorem mul_squareBound_le (left right : Bounds) :
    (Interval.Arithmetic.mul left right).squareBound ≤ left.squareBound * right.squareBound := by
  apply (hull_squareBound_le _ _).trans
  apply Order.Basic.max_le
  · exact (scale_squareBound_le left.lower right).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by rewrite [Interval.Bounds.squareBound_eq]; exact Order.Basic.le_max_left _ _)
        right.squareBound_nonneg)
  · exact (scale_squareBound_le left.upper right).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by rewrite [Interval.Bounds.squareBound_eq]; exact Order.Basic.le_max_right _ _)
        right.squareBound_nonneg)

/-- Translating an interval bounds its endpoint squares by twice the sum of the original square bound and the
translation square.

The squared sum inequality bounds each translated endpoint. Its
original endpoint square is bounded by the retained interval square bound. -/
public theorem addConstant_squareBound_le (interval : Bounds) (coefficient : Fraction.Rational) :
    (Interval.Arithmetic.addConstant interval coefficient).squareBound ≤ 2 * (interval.squareBound + coefficient ^ 2) :=
      by
  rewrite [Interval.Bounds.squareBound_eq (Interval.Arithmetic.addConstant interval coefficient)]
  apply Order.Basic.max_le
  · exact (Square.add_sq_le_two interval.lower coefficient).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct
          (interval.sq_le_squareBound ⟨Order.Basic.le_refl _, interval.valid⟩)
          (Order.Basic.le_refl _))
        (by decide))
  · exact (Square.add_sq_le_two interval.upper coefficient).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct
          (interval.sq_le_squareBound ⟨interval.valid, Order.Basic.le_refl _⟩)
          (Order.Basic.le_refl _))
        (by decide))

end Purelib.Data.Rat.Interval.Arithmetic.Bounds
