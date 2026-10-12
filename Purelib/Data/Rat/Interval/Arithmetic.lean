module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Data.Rat.Interval.Arithmetic

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

/-- Construct the singleton closed rational interval at the supplied value.

The two retained endpoints are the supplied rational itself. The validity
witness is reflexivity in the original rational order. -/
@[expose] public def constant (value : Fraction.Rational) : Bounds := ⟨value, value, le_rfl⟩

/-- Construct the least endpoint hull containing both retained rational intervals.

Take the smaller lower endpoint and the larger upper endpoint. The validity witness is transported from the original
input bounds, and containment retains both input intervals unchanged. -/
@[expose] public def hull (left right : Bounds) : Bounds :=
  ⟨min left.lower right.lower, max left.upper right.upper,
    (Order.Basic.min_le_left _ _).trans (left.valid.trans (Order.Basic.le_max_left _ _))⟩

/-- The hull contains every value contained in its left interval.

The hull retains the minimum of both lower endpoints and the maximum of
both upper endpoints. The supplied left containment bounds transport
through those same endpoint comparisons. -/
public theorem hull_contains_left (left right : Bounds) {value : Fraction.Rational}
    (inside : left.Contains value) : (Interval.Arithmetic.hull left right).Contains value :=
  ⟨(Order.Basic.min_le_left _ _).trans inside.1, inside.2.trans (Order.Basic.le_max_left _ _)⟩

/-- The hull contains every value contained in its right interval.

The hull retains the minimum of both lower endpoints and the maximum of
both upper endpoints. The supplied right containment bounds transport
through those same endpoint comparisons. -/
public theorem hull_contains_right (left right : Bounds) {value : Fraction.Rational}
    (inside : right.Contains value) : (Interval.Arithmetic.hull left right).Contains value :=
  ⟨(Order.Basic.min_le_right _ _).trans inside.1, inside.2.trans (Order.Basic.le_max_right _ _)⟩

/-- Translate both rational interval endpoints by the same supplied rational.

Both original endpoints receive the same rational shift. Weak translation
transports their stored order witness to the translated interval. -/
@[expose] public def addConstant (interval : Bounds) (value : Fraction.Rational) :
  Bounds :=
  ⟨interval.lower + value, interval.upper + value, add_le_add interval.valid le_rfl⟩

/-- Translating an interval retains containment of the correspondingly translated value.

The original lower and upper containment comparisons receive the same
shift. The retained translated endpoints therefore contain the shifted value. -/
public theorem addConstant_contains (interval : Bounds) (shift : Fraction.Rational) {value :
  Fraction.Rational}
    (inside : interval.Contains value) : (Interval.Arithmetic.addConstant interval shift).Contains (value + shift) :=
  ⟨add_le_add inside.1 le_rfl, add_le_add inside.2 le_rfl⟩

/-- Construct a rational interval enclosing all products of a fixed scalar with the original interval.

Multiply the two retained endpoints by the scalar and order the resulting endpoints using minimum and maximum. This
handles positive, zero and negative scalars uniformly while preserving an explicit validity proof. -/
@[expose] public def scale (factor : Fraction.Rational) (interval : Bounds) : Bounds
  :=
  ⟨min (factor * interval.lower) (factor * interval.upper),
    max (factor * interval.lower) (factor * interval.upper),
    (Order.Basic.min_le_left _ _).trans (Order.Basic.le_max_left _ _)⟩

/-- Scaling a rational interval retains containment of the correspondingly scaled value.

The sign of the retained factor determines which endpoint product is
lower. Direct rational multiplication bounds preserve the supplied
containment in that same sign branch. -/
public theorem scale_contains (factor : Fraction.Rational) (interval : Bounds) {value :
  Fraction.Rational}
    (inside : interval.Contains value) : (Interval.Arithmetic.scale factor interval).Contains (factor * value) := by
  by_cases nonnegative : 0 ≤ factor
  · exact ⟨(Order.Basic.min_le_left _ _).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.1 nonnegative),
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2 nonnegative).trans
        (Order.Basic.le_max_right _ _)⟩
  · have nonpositive : factor ≤ 0 := le_of_not_ge nonnegative
    exact ⟨(Order.Basic.min_le_right _ _).trans
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonpositive_left inside.2 nonpositive),
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonpositive_left inside.1 nonpositive).trans
        (Order.Basic.le_max_left _ _)⟩

/-- Construct the endpoint hull of the two scalar multiples of the right rational interval.

Scale the right interval by the left lower and upper endpoints, then retain the hull of those exact endpoint products.
The resulting interval contains every product of input values regardless of their signs. -/
@[expose] public def mul (left right : Bounds) : Bounds :=
  Interval.Arithmetic.hull (Interval.Arithmetic.scale left.lower right) (Interval.Arithmetic.scale left.upper right)

/-- The interval product contains the product of any two values retained by the input intervals.

The original left endpoint products enclose the scaled right value.
The sign of the right value transports the supplied left containment
between those retained product endpoints. -/
public theorem mul_contains (left right : Bounds) {first second : Fraction.Rational}
    (firstInside : left.Contains first) (secondInside : right.Contains second) :
    (Interval.Arithmetic.mul left right).Contains (first * second) := by
  have lowerEndpoint := Interval.Arithmetic.hull_contains_left (Interval.Arithmetic.scale left.lower right)
    (Interval.Arithmetic.scale left.upper right)
    (Interval.Arithmetic.scale_contains left.lower right secondInside)
  have upperEndpoint := Interval.Arithmetic.hull_contains_right (Interval.Arithmetic.scale left.lower right)
    (Interval.Arithmetic.scale left.upper right)
    (Interval.Arithmetic.scale_contains left.upper right secondInside)
  by_cases nonnegative : 0 ≤ second
  · exact ⟨lowerEndpoint.1.trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct firstInside.1 nonnegative),
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct firstInside.2 nonnegative).trans
        upperEndpoint.2⟩
  · have nonpositive : second ≤ 0 := le_of_not_ge nonnegative
    exact ⟨upperEndpoint.1.trans (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonpositive_right
      firstInside.2 nonpositive),
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonpositive_right firstInside.1 nonpositive).trans
        lowerEndpoint.2⟩

end Purelib.Data.Rat.Interval.Arithmetic
