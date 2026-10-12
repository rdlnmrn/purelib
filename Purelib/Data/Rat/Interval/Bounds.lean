module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Endpoint-square bounds for rational intervals

Endpoint squares bound every retained coordinate between those endpoints.
The same scalar comparison controls interval differences and refinement.
-/

open Purelib
open Purelib.Data.Rat

namespace Purelib.Geometry.Rational.Box

/-- A rational between two endpoints has square at most the larger endpoint square.

The two retained endpoint comparisons locate the original rational value.
Its sign chooses the nonnegative endpoint or the negated nonpositive endpoint,
and direct multiplication comparisons bound its square. -/
public theorem sq_le_endpoint_max {lower value upper : Fraction.Rational}
    (hlower : lower ≤ value) (hupper : value ≤ upper) :
    value ^ 2 ≤ max (lower ^ 2) (upper ^ 2) := by
  by_cases hvalue : 0 ≤ value
  · have hupperNonnegative : 0 ≤ upper := hvalue.trans hupper
    have hfirst : value * value ≤ upper * value :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct hupper hvalue
    have hsecond : value * upper ≤ upper * upper :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        hupper hupperNonnegative
    have hsquare : value ^ 2 ≤ upper ^ 2 := by
      rw [pow_two, pow_two]
      exact hfirst.trans (by
        rw [Fraction.Field.mul_comm upper value]
        exact hsecond)
    exact hsquare.trans (Fraction.Order.Basic.le_max_right _ _)
  · have hvalueNonpositive : value ≤ 0 :=
      Fraction.Order.Arithmetic.le_of_not_gt_direct fun positive => hvalue positive.1
    have hlowerNonpositive : lower ≤ 0 := hlower.trans hvalueNonpositive
    have hneg : -value ≤ -lower := Fraction.Order.Arithmetic.neg_le_neg_direct hlower
    have hnegValueNonnegative : 0 ≤ -value := by
      have comparison := Fraction.Order.Arithmetic.neg_le_neg_direct hvalueNonpositive
      rw [show -(0 : Fraction.Rational) = 0 by decide] at comparison
      exact comparison
    have hnegLowerNonnegative : 0 ≤ -lower := by
      have comparison := Fraction.Order.Arithmetic.neg_le_neg_direct hlowerNonpositive
      rw [show -(0 : Fraction.Rational) = 0 by decide] at comparison
      exact comparison
    have hfirst : (-value) * (-value) ≤ (-lower) * (-value) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        hneg hnegValueNonnegative
    have hsecond : (-value) * (-lower) ≤ (-lower) * (-lower) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        hneg hnegLowerNonnegative
    have hsquare : value ^ 2 ≤ lower ^ 2 := by
      rw [pow_two, pow_two]
      calc
        value * value = (-value) * (-value) := by ring1
        _ ≤ (-lower) * (-value) := hfirst
        _ = (-value) * (-lower) := Fraction.Field.mul_comm _ _
        _ ≤ (-lower) * (-lower) := hsecond
        _ = lower * lower := by ring1
    exact hsquare.trans (Fraction.Order.Basic.le_max_left _ _)

end Purelib.Geometry.Rational.Box

namespace Purelib.Data.Rat.Interval

/-- The squared difference of two contained rationals is at most the squared interval width.

Both original values lie between the same ordered interval endpoints.
Their difference lies between the negative and positive interval width,
so its square is at most the retained width square. -/
public theorem parameter_sub_sq_le_width_sq
    (interval : Bounds) {left right : Fraction.Rational}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    (left - right) ^ 2 ≤
      (Bounds.width interval) ^ 2 := by
  let width := Bounds.width interval
  have lower : -width ≤ left - right := by
    dsimp only [width, Bounds.width]
    calc
      -(interval.upper - interval.lower) =
          interval.lower + -interval.upper := by ring1
      _ ≤ left + -right := add_le_add leftInside.1
        (Fraction.Order.Arithmetic.neg_le_neg_direct rightInside.2)
      _ = left - right := by ring1
  have upper : left - right ≤ width := by
    dsimp only [width, Bounds.width]
    calc
      left - right = left + -right := by ring1
      _ ≤ interval.upper + -interval.lower := add_le_add leftInside.2
        (Fraction.Order.Arithmetic.neg_le_neg_direct rightInside.1)
      _ = interval.upper - interval.lower := by ring1
  have square := Geometry.Rational.Box.sq_le_endpoint_max lower upper
  have negSquare : (-width) ^ 2 = width ^ 2 := by ring1
  rw [negSquare, Fraction.Order.Basic.max_self] at square
  exact square

end Purelib.Data.Rat.Interval

namespace Purelib.Data.Rat.Interval.Bounds

/-- Compute the maximum of the two retained endpoint squares.

The original lower and upper endpoint squares determine the retained maximum.
No endpoint, coordinate or comparison operation is replaced. -/
@[expose] public def squareBound (interval : Bounds) : Fraction.Rational :=
  max (interval.lower ^ 2) (interval.upper ^ 2)

/-- The endpoint-square bound is nonnegative.

The lower endpoint square is nonnegative and lies below the retained
maximum, giving the same scalar square bound a nonnegative floor. -/
public theorem squareBound_nonneg (interval : Bounds) : 0 ≤ interval.squareBound :=
  (Fraction.Order.Arithmetic.sq_nonneg_direct interval.lower).trans
    (Fraction.Order.Basic.le_max_left _ _)

/-- The square of a contained rational is at most the interval's endpoint-square bound.

The retained containment comparisons bound the original coordinate
between both endpoints. Its square is below their retained maximum. -/
public theorem sq_le_squareBound {interval : Bounds} {x : Fraction.Rational}
    (inside : interval.Contains x) : x ^ 2 ≤ interval.squareBound :=
  Geometry.Rational.Box.sq_le_endpoint_max inside.1 inside.2

/-- Endpoint refinement cannot increase the interval's square bound.

The inner endpoints lie in the original outer interval. Their square
bounds combine under the same maximum operation to compare the two intervals. -/
public theorem squareBound_le_of_refines {interval root : Bounds}
    (refines : interval.Refines root) :
    interval.squareBound ≤ root.squareBound := by
  apply Fraction.Order.Basic.max_le
  · exact root.sq_le_squareBound ⟨refines.1, interval.valid.trans refines.2⟩
  · exact root.sq_le_squareBound ⟨refines.1.trans interval.valid, refines.2⟩

end Purelib.Data.Rat.Interval.Bounds
