module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bounds
public import Purelib.Data.Rat.Interval.Width
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Data.Rat.Interval.Radius

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Compute the largest squared displacement of an interval endpoint from a supplied sample.

Take the maximum of the two endpoint displacement squares. Containment then bounds the squared displacement of every
interval member from the same supplied sample, even when the sample is outside the interval. -/
@[expose] public def sampleRadiusSq (interval : Bounds) (sample : Fraction.Rational) :
  Fraction.Rational :=
  max ((interval.lower - sample) ^ 2) ((interval.upper - sample) ^ 2)

/-- The squared sample radius at the lower endpoint equals the squared interval width.

The retained lower endpoint has zero displacement from itself. The
other endpoint displacement is the original interval width, whose
nonnegative square is selected by the same rational maximum. -/
public theorem sampleRadiusSq_lower_eq_widthSq (interval : Bounds) :
    sampleRadiusSq interval interval.lower =
      (interval.upper - interval.lower) ^ 2 := by
  unfold sampleRadiusSq
  have nonnegative : 0 ≤ (interval.upper - interval.lower) ^ 2 :=
    Arithmetic.sq_nonneg_direct _
  have zeroSq : (0 : Fraction.Rational) ^ 2 = 0 := by ring1
  simp only [sub_self, zeroSq]
  exact Fraction.Order.Basic.max_eq_right nonnegative

/-- Sampling at either endpoint gives the same squared interval radius.

At either endpoint one displacement vanishes and the other is the
original width or its negation. The retained maxima select their
nonnegative squares, which are equal. -/
public theorem sampleRadiusSq_upper_eq_lower (interval : Bounds) :
    sampleRadiusSq interval interval.upper =
      sampleRadiusSq interval interval.lower := by
  unfold sampleRadiusSq
  have forwardNonnegative :
      0 ≤ (interval.upper - interval.lower) ^ 2 :=
    Arithmetic.sq_nonneg_direct _
  have reverseNonnegative :
      0 ≤ (interval.lower - interval.upper) ^ 2 :=
    Arithmetic.sq_nonneg_direct _
  have zeroSq : (0 : Fraction.Rational) ^ 2 = 0 := by ring1
  simp only [sub_self, zeroSq]
  rw [Fraction.Order.Basic.max_eq_left reverseNonnegative, Fraction.Order.Basic.max_eq_right forwardNonnegative]
  ring1

/-- Every contained rational has squared displacement from the sample at most the endpoint-based squared radius.

The two retained containment comparisons bound the shifted rational
between the shifted original endpoints. Their same squared endpoint
maximum is the original sample radius. -/
public theorem sub_sq_le_sampleRadiusSq
    (interval : Bounds) {sample x : Fraction.Rational}
    (inside : interval.Contains x) :
    (x - sample) ^ 2 ≤ sampleRadiusSq interval sample := by
  exact Geometry.Rational.Box.sq_le_endpoint_max
    (Arithmetic.sub_le_sub_right_direct inside.1 sample) (Arithmetic.sub_le_sub_right_direct inside.2 sample)

/-- A proper interval with width below both one and the radius bound has squared lower-endpoint radius below that bound.

The proper interval has positive retained width. Its bound below one
makes its square strictly smaller, while its bound below the supplied
radius transports the same squared endpoint displacement. -/
public theorem EventPartition.sampleRadiusSq_lt_of_width_lt
    {interval : Bounds} (proper : interval.lower < interval.upper)
    {radiusBound : Fraction.Rational}
    (widthSmall : Bounds.width interval < min 1 radiusBound) :
    sampleRadiusSq interval interval.lower <
      radiusBound := by
  let width := Bounds.width interval
  have widthPositive : 0 < width := Bounds.width_pos proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have widthBelowRadius : width < radiusBound :=
    widthSmall.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have squareBelowWidth : width ^ 2 < width := by
    have multiplied :=
      Arithmetic.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    simpa only [pow_two, one_mul] using multiplied
  rw [sampleRadiusSq_lower_eq_widthSq]
  exact squareBelowWidth.trans widthBelowRadius

/-- A proper interval with width below both one and the radius bound has squared lower-endpoint radius below that bound.

The proper interval has positive original endpoint difference. Its
bound below one makes its square smaller, while its second retained
width bound places that square below the supplied radius. -/
public theorem Partition.radius_lt_of_width_lt
    {interval : Bounds} (proper : interval.lower < interval.upper)
    {radiusBound : Fraction.Rational}
    (widthSmall : interval.upper - interval.lower < min 1 radiusBound) :
    sampleRadiusSq interval interval.lower < radiusBound := by
  let width := interval.upper - interval.lower
  have widthPositive : 0 < width :=
    Arithmetic.sub_pos_direct proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have widthBelowRadius : width < radiusBound :=
    widthSmall.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have squareBelowWidth : width ^ 2 < width := by
    have multiplied :=
      Arithmetic.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    simpa only [pow_two, one_mul] using multiplied
  rw [sampleRadiusSq_lower_eq_widthSq]
  exact squareBelowWidth.trans widthBelowRadius

/-- The squared sample radius at the lower endpoint is nonnegative.

The retained lower-endpoint displacement has a nonnegative square.
The original endpoint maximum bounds that same square from above. -/
public theorem sampleRadiusSq_nonneg (interval : Bounds) :
    0 ≤ sampleRadiusSq interval interval.lower :=
  (Arithmetic.sq_nonneg_direct
      (interval.lower - interval.lower)).trans (Fraction.Order.Basic.le_max_left _ _)

end Purelib.Data.Rat.Interval.Radius
