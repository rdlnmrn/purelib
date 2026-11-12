module
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Quantitative comparison of rational interval readings

Two retained interval readings can be compared through another pair of
readings in those same intervals, with their actual discrepancy retained.
-/

public section

namespace Purelib.Data.Rat.Interval

open Purelib.Data.Rat

/-- Bound two interval readings by both widths and the discrepancy of two retained comparison readings.

Each comparison reading lies in its own original interval. The result uses
both directed endpoint bounds and the absolute discrepancy of those readings. -/
theorem abs_sub_le_of_readings {left right : Interval} {leftValue rightValue leftReading rightReading :
    Fraction.Rational} (leftInside : left.Contains leftValue) (rightInside : right.Contains rightValue)
    (leftReadInside : left.Contains leftReading) (rightReadInside : right.Contains rightReading) :
    Fraction.abs (leftValue - rightValue) ≤ left.width + right.width + Fraction.abs (leftReading - rightReading) := by
  have leftBounds := pairwise_difference_le leftInside leftReadInside
  have rightBounds := pairwise_difference_le rightInside rightReadInside
  have forwardPoint : leftReading - rightReading ≤ Fraction.abs (leftReading - rightReading) :=
    Fraction.Order.Basic.le_max_left _ _
  have backwardPoint : rightReading - leftReading ≤ Fraction.abs (leftReading - rightReading) := by
    have reverse : rightReading - leftReading = -(leftReading - rightReading) := by ring1
    rw [reverse]
    exact Fraction.Order.Basic.le_max_right _ _
  have forward : leftValue - rightValue ≤ left.width + right.width + Fraction.abs (leftReading - rightReading) := by
    calc
      leftValue - rightValue =
          (leftValue - leftReading) + (leftReading - rightReading) + (rightReading - rightValue) := by ring1
      _ ≤ (left.width + Fraction.abs (leftReading - rightReading)) + right.width :=
        Fraction.Order.Arithmetic.add_le_add_direct
          (Fraction.Order.Arithmetic.add_le_add_direct leftBounds.1 forwardPoint) rightBounds.2
      _ = _ := by ring1
  have backward : rightValue - leftValue ≤ left.width + right.width + Fraction.abs (leftReading - rightReading) := by
    calc
      rightValue - leftValue =
          (rightValue - rightReading) + (rightReading - leftReading) + (leftReading - leftValue) := by ring1
      _ ≤ (right.width + Fraction.abs (leftReading - rightReading)) + left.width :=
        Fraction.Order.Arithmetic.add_le_add_direct
          (Fraction.Order.Arithmetic.add_le_add_direct rightBounds.1 backwardPoint) leftBounds.2
      _ = _ := by ring1
  change max (leftValue - rightValue) (-(leftValue - rightValue)) ≤ _
  apply Fraction.Order.Basic.max_le forward
  have reverse : -(leftValue - rightValue) = rightValue - leftValue := by ring1
  rw [reverse]
  exact backward

/-- Overlapping intervals bound the absolute difference of any two of their readings by their combined widths. -/
theorem abs_sub_le_of_overlaps {left right : Interval} {leftValue rightValue : Fraction.Rational}
    (leftInside : left.Contains leftValue) (rightInside : right.Contains rightValue)
    (overlaps : left.Overlaps right) : Fraction.abs (leftValue - rightValue) ≤ left.width + right.width := by
  have common := overlapWitness_inside overlaps
  have comparison := abs_sub_le_of_readings leftInside rightInside common.1 common.2
  have difference : left.overlapWitness right - left.overlapWitness right = 0 := by ring1
  rw [difference] at comparison
  change Fraction.abs (leftValue - rightValue) ≤ left.width + right.width + 0 at comparison
  have sum : left.width + right.width + 0 = left.width + right.width := by ring1
  rw [sum] at comparison
  exact comparison

/-- Two ranges meeting one observation interval are compared using its actual width.

The overlap witnesses are rational readings of the two original ranges and
the same retained observation interval. Their discrepancy is bounded by the
width of that interval, without selecting a completed common value. -/
theorem abs_sub_le_of_shared_overlap {left right observation : Interval}
    {leftValue rightValue : Fraction.Rational} (leftInside : left.Contains leftValue)
    (rightInside : right.Contains rightValue) (leftOverlap : left.Overlaps observation)
    (rightOverlap : right.Overlaps observation) :
    Fraction.abs (leftValue - rightValue) ≤ left.width + right.width + observation.width := by
  have leftWitness := overlapWitness_inside leftOverlap
  have rightWitness := overlapWitness_inside rightOverlap
  have comparison := abs_sub_le_of_readings leftInside rightInside leftWitness.1 rightWitness.1
  have observationBounds := pairwise_difference_le leftWitness.2 rightWitness.2
  have discrepancy : Fraction.abs (left.overlapWitness observation - right.overlapWitness observation) ≤
      observation.width := by
    change max (left.overlapWitness observation - right.overlapWitness observation)
      (-(left.overlapWitness observation - right.overlapWitness observation)) ≤ observation.width
    apply Fraction.Order.Basic.max_le observationBounds.1
    have reverse : -(left.overlapWitness observation - right.overlapWitness observation) =
        right.overlapWitness observation - left.overlapWitness observation := by ring1
    rw [reverse]
    exact observationBounds.2
  exact comparison.trans (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) discrepancy)

end Purelib.Data.Rat.Interval

end
