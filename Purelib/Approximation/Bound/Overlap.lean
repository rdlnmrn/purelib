module
public import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Overlap forced by finite point requests

Two rational intervals that overlap every state of the same arbitrarily
refinable process must overlap one another. A single finite request at a
positive gap rules out disjoint intervals; no completed intersection is used.
-/

public section

namespace Purelib.Approximation.BoundProcess

open Purelib.Data.Rat

/-- One endpoint bound forced by overlap with every finite state of the same process. -/
private theorem lower_le_upper_of_overlap_all (process : BoundProcess)
    (left right : Purelib.Data.Rat.Interval)
    (leftOverlap : ∀ state, left.Overlaps (process.bound state))
    (rightOverlap : ∀ state, right.Overlaps (process.bound state)) : left.lower ≤ right.upper := by
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro separated
  have gapPositive : 0 < left.lower - right.upper := Fraction.Order.Arithmetic.sub_pos_direct separated
  let state := process.request process.initial (left.lower - right.upper) gapPositive
  have first := leftOverlap state
  have second := rightOverlap state
  have gapBound := Fraction.Order.Arithmetic.sub_le_sub_direct first.1 second.2
  have small := process.accurate process.initial (left.lower - right.upper) gapPositive
  exact (not_lt_of_ge gapBound) small

/-- Two rational intervals overlapping every finite process state overlap each other.

If either pair of endpoints were separated by a positive rational gap, the
original process could be requested to a narrower interval. That interval
cannot meet both original ranges, contradicting their actual admission laws. -/
theorem overlaps_of_overlap_all (process : BoundProcess) (left right : Purelib.Data.Rat.Interval)
    (leftOverlap : ∀ state, left.Overlaps (process.bound state))
    (rightOverlap : ∀ state, right.Overlaps (process.bound state)) : left.Overlaps right :=
  ⟨lower_le_upper_of_overlap_all process left right leftOverlap rightOverlap,
    lower_le_upper_of_overlap_all process right left rightOverlap leftOverlap⟩

end Purelib.Approximation.BoundProcess

end
