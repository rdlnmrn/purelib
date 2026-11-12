module
public import Purelib.Data.Rat.Interval.Basic

/-!
# Intersection of overlapping rational intervals

Two retained overlapping intervals determine the larger lower endpoint and
the smaller upper endpoint. Their original overlap proof certifies that the
computed endpoints remain ordered.
-/

public section

namespace Purelib.Data.Rat.Interval

open Purelib.Data.Rat

/-- Intersect two retained rational intervals using their explicit overlap certificate. -/
@[expose] def intersect (left right : Interval) (overlaps : left.Overlaps right) : Interval where
  lower := max left.lower right.lower
  upper := min left.upper right.upper
  valid := Fraction.Order.Basic.max_le
    (Fraction.Order.Basic.le_min left.valid overlaps.1)
    (Fraction.Order.Basic.le_min overlaps.2 right.valid)

/-- The computed intersection refines the original left interval. -/
theorem intersect_refines_left (left right : Interval) (overlaps : left.Overlaps right) :
    Refines (left.intersect right overlaps) left :=
  ⟨Fraction.Order.Basic.le_max_left _ _, Fraction.Order.Basic.min_le_left _ _⟩

/-- The computed intersection refines the original right interval. -/
theorem intersect_refines_right (left right : Interval) (overlaps : left.Overlaps right) :
    Refines (left.intersect right overlaps) right :=
  ⟨Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.min_le_right _ _⟩

/-- A rational belongs to the intersection exactly when both original intervals contain it. -/
theorem intersect_contains_iff (left right : Interval) (overlaps : left.Overlaps right) (value : Fraction.Rational) :
    (left.intersect right overlaps).Contains value ↔ left.Contains value ∧ right.Contains value := by
  constructor
  · intro inside
    exact ⟨(intersect_refines_left left right overlaps).contains inside,
      (intersect_refines_right left right overlaps).contains inside⟩
  · intro inside
    exact ⟨Fraction.Order.Basic.max_le inside.1.1 inside.2.1,
      Fraction.Order.Basic.le_min inside.1.2 inside.2.2⟩

/-- The intersection overlaps any interval overlapping both original intervals.

The original intervals must overlap to construct their intersection. The
two additional endpoint comparisons give the overlap with the third interval
directly, without selecting a point from any completed object. -/
theorem intersect_overlaps (left right other : Interval) (overlaps : left.Overlaps right)
    (leftOverlap : left.Overlaps other) (rightOverlap : right.Overlaps other) :
    (left.intersect right overlaps).Overlaps other :=
  ⟨Fraction.Order.Basic.max_le leftOverlap.1 rightOverlap.1,
    Fraction.Order.Basic.le_min leftOverlap.2 rightOverlap.2⟩

/-- The intersection's width is no greater than either original width. -/
theorem intersect_width_le (left right : Interval) (overlaps : left.Overlaps right) :
    (left.intersect right overlaps).width ≤ left.width ∧ (left.intersect right overlaps).width ≤ right.width :=
  ⟨(intersect_refines_left left right overlaps).width_le, (intersect_refines_right left right overlaps).width_le⟩

end Purelib.Data.Rat.Interval

end
