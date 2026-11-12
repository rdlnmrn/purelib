module
public import Purelib.Integration.Partition.Length
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Rat.Sum
import Purelib.Data.List.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Rational neighborhoods for exceptional partition points

A symmetric rational neighborhood is clipped to the unit interval. Every
short cell containing the original point lies in that clipped neighborhood;
its width is bounded by twice the supplied radius.
-/

public section

namespace Purelib.Integration.Partition.Interval

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Decide whether a rational point lies in the original closed interval. -/
@[expose] def touches (interval : Interval) (point : Fraction.Rational) : Bool :=
  decide (interval.start ≤ point ∧ point ≤ interval.finish)

/-- The Boolean test agrees with the original closed endpoint comparisons. -/
theorem touches_iff (interval : Interval) (point : Fraction.Rational) :
    interval.touches point = true ↔ interval.start ≤ point ∧ point ≤ interval.finish := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- Decide whether a closed interval contains any point in the original finite list. -/
@[expose] def marked (interval : Interval) (points : List Fraction.Rational) : Bool :=
  points.any interval.touches

/-- A marked interval contains an actual retained exceptional point. -/
theorem marked_iff (interval : Interval) (points : List Fraction.Rational) :
    interval.marked points = true ↔ ∃ point ∈ points, interval.start ≤ point ∧ point ≤ interval.finish := by
  constructor
  · intro marked
    rcases (Purelib.Data.List.Search.any_iff interval.touches points).mp marked with ⟨point, member, touches⟩
    exact ⟨point, member, (interval.touches_iff point).mp touches⟩
  · rintro ⟨point, member, inside⟩
    exact (Purelib.Data.List.Search.any_iff interval.touches points).mpr
      ⟨point, member, (interval.touches_iff point).mpr inside⟩

/-- Clip the symmetric neighborhood of a rational point to the unit interval. -/
@[expose] def neighborhood (point radius : Fraction.Rational) : Interval :=
  let unit : Interval := ⟨0, 1⟩
  ⟨unit.clamp (point - radius), unit.clamp (point + radius)⟩

/-- A nonnegative radius produces ordered neighborhood endpoints in the unit interval. -/
theorem neighborhood_bounds (point radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    0 ≤ (neighborhood point radius).start ∧
      (neighborhood point radius).start ≤ (neighborhood point radius).finish ∧
        (neighborhood point radius).finish ≤ 1 := by
  let unit : Interval := ⟨0, 1⟩
  have unitOrdered : unit.start ≤ unit.finish := by
    change (0 : Fraction.Rational) ≤ 1
    decide
  have signed := Arithmetic.neg_le_self_of_nonnegative nonnegative
  have shifted := Arithmetic.add_le_add_right_direct signed point
  have original : point - radius ≤ point + radius := by
    have first : -radius + point = point - radius := by ring1
    have second : radius + point = point + radius := by ring1
    rw [first, second] at shifted
    exact shifted
  exact ⟨(unit.clamp_bounds unitOrdered (point - radius)).1, unit.clamp_mono original,
    (unit.clamp_bounds unitOrdered (point + radius)).2⟩

/-- A unit-interval point's clipped neighborhood has length at most twice its radius. -/
theorem neighborhood_length_le (point radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (lower : 0 ≤ point) (upper : point ≤ 1) : (neighborhood point radius).signedLength ≤ radius + radius := by
  let unit : Interval := ⟨0, 1⟩
  have negative := Arithmetic.neg_le_neg_direct nonnegative
  rw [neg_zero] at negative
  have shifted := Arithmetic.add_le_add_right_direct negative point
  have subLePoint : point - radius ≤ point := by
    have first : -radius + point = point - radius := by ring1
    rw [first, Fraction.Field.zero_add] at shifted
    exact shifted
  have subLeOne := Fraction.Order.Basic.le_trans _ _ _ subLePoint upper
  have addNonnegative := Arithmetic.add_le_add_direct lower nonnegative
  change (0 : Fraction.Rational) ≤ point + radius at addNonnegative
  have lowerClamp : point - radius ≤ unit.clamp (point - radius) := by
    change point - radius ≤ max 0 (min 1 (point - radius))
    rw [Fraction.Order.Basic.min_eq_right subLeOne]
    exact Fraction.Order.Basic.le_max_right _ _
  have upperClamp : unit.clamp (point + radius) ≤ point + radius := by
    change max 0 (min 1 (point + radius)) ≤ point + radius
    exact Fraction.Order.Basic.max_le addNonnegative (Fraction.Order.Basic.min_le_right _ _)
  have bound := Arithmetic.sub_le_sub_direct upperClamp lowerClamp
  have width : (point + radius) - (point - radius) = radius + radius := by ring1
  rw [width] at bound
  exact bound

/-- A short unit child containing the point lies in its clipped symmetric neighborhood.

The child's two endpoints are within its own length of the retained point.
Clamping both endpoint comparisons to the unit interval preserves containment. -/
theorem neighborhood_contains_child (point radius : Fraction.Rational) (child : Interval) (valid : child.Valid)
    (inside : child.start ≤ point ∧ point ≤ child.finish) (small : child.signedLength < radius) :
    (neighborhood point radius).start ≤ child.start ∧ child.finish ≤ (neighborhood point radius).finish := by
  let unit : Interval := ⟨0, 1⟩
  have firstDistance : point - child.start ≤ child.signedLength :=
    Arithmetic.sub_le_sub_direct inside.2 (Fraction.Order.Basic.le_refl _)
  have secondDistance : child.finish - point ≤ child.signedLength :=
    Arithmetic.sub_le_sub_direct (Fraction.Order.Basic.le_refl _) inside.1
  have firstBound := Fraction.Order.Basic.le_trans _ _ _ firstDistance small.le
  have secondBound := Fraction.Order.Basic.le_trans _ _ _ secondDistance small.le
  have firstAdded := Arithmetic.sub_le_iff_le_add_direct.mp firstBound
  have firstCommute : radius + child.start = child.start + radius := by ring1
  rw [firstCommute] at firstAdded
  have before : point - radius ≤ child.start := Arithmetic.sub_le_iff_le_add_direct.mpr firstAdded
  have after := Arithmetic.sub_le_iff_le_add_direct.mp secondBound
  have secondCommute : radius + point = point + radius := by ring1
  rw [secondCommute] at after
  have clampedBefore := unit.clamp_mono before
  have clampedAfter := unit.clamp_mono after
  have startInside : 0 ≤ child.start ∧ child.start ≤ 1 := ⟨valid.1, valid.2.1.le.trans valid.2.2⟩
  have finishInside : 0 ≤ child.finish ∧ child.finish ≤ 1 := ⟨valid.1.trans valid.2.1.le, valid.2.2⟩
  rw [unit.clamp_inside child.start startInside.1 startInside.2] at clampedBefore
  rw [unit.clamp_inside child.finish finishInside.1 finishInside.2] at clampedAfter
  exact ⟨clampedBefore, clampedAfter⟩

end Purelib.Integration.Partition.Interval

namespace Purelib.Integration.Partition.Unit.Normalized

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.List.Rat.Linear
open Purelib.Integration.Partition

/-- Sum the original lengths of cells whose closed intervals contain the rational point. -/
@[expose] def touchLength (partition : Normalized) (point : Fraction.Rational) : Fraction.Rational :=
  (partition.intervals.map (fun interval => if interval.touches point then interval.signedLength else 0)).sum

/-- Sum the original lengths of cells marked by at least one retained exceptional point. -/
@[expose] def markedLength (partition : Normalized) (points : List Fraction.Rational) : Fraction.Rational :=
  (partition.intervals.map (fun interval => if interval.marked points then interval.signedLength else 0)).sum

/-- Cells touching one point have total length at most twice the strictly larger mesh radius.

The closed cells lie inside the clipped symmetric neighborhood of that point.
Their lengths are bounded by the clamped lengths of the complete original
partition, which telescope exactly even at endpoints. -/
theorem touchLength_le (partition : Normalized) (point radius : Fraction.Rational) (positive : 0 < radius)
    (small : ∀ interval ∈ partition.intervals, interval.signedLength < radius) :
    partition.touchLength point ≤ radius + radius := by
  let neighborhood := Partition.Interval.neighborhood point radius
  have nonnegative : 0 ≤ radius + radius := by
    have sum := Arithmetic.add_le_add_direct positive.le positive.le
    change (0 : Fraction.Rational) ≤ radius + radius at sum
    exact sum
  by_cases inside : 0 ≤ point ∧ point ≤ 1
  · have validNeighborhood := Partition.Interval.neighborhood_bounds point radius positive.le
    have each : ∀ interval ∈ partition.intervals,
        (if interval.touches point then interval.signedLength else 0) ≤ neighborhood.clampedLength interval := by
      intro interval member
      have valid := partition.valid interval member
      cases accepted : interval.touches point with
      | false =>
          change (0 : Fraction.Rational) ≤ neighborhood.clampedLength interval
          exact neighborhood.clampedLength_nonnegative interval valid.2.1.le
      | true =>
          change interval.signedLength ≤ neighborhood.clampedLength interval
          have contains := (interval.touches_iff point).mp accepted
          have located := Partition.Interval.neighborhood_contains_child point radius interval valid contains
            (small interval member)
          have equal := neighborhood.clamp_child_length interval located.1 valid.2.1.le located.2
          change neighborhood.clampedLength interval = interval.signedLength at equal
          rewrite [equal]
          exact Fraction.Order.Basic.le_refl _
    have sumBound := sum_le (fun interval => if interval.touches point then interval.signedLength else 0)
      (fun interval => neighborhood.clampedLength interval) partition.intervals each
    have total := partition.clampedLength_sum_of_bounds neighborhood validNeighborhood.1 validNeighborhood.2.1
      validNeighborhood.2.2
    rw [total] at sumBound
    exact Fraction.Order.Basic.le_trans _ _ _ sumBound
      (Partition.Interval.neighborhood_length_le point radius positive.le inside.1 inside.2)
  · have rejected : ∀ interval ∈ partition.intervals, interval.touches point = false := by
      intro interval member
      cases accepted : interval.touches point with
      | false => rfl
      | true =>
          have located := (interval.touches_iff point).mp accepted
          have valid := partition.valid interval member
          exact (inside ⟨valid.1.trans located.1, located.2.trans valid.2.2⟩).elim
    have empty := sum_congr (fun interval => if interval.touches point then interval.signedLength else 0)
      (fun _ => (0 : Fraction.Rational)) partition.intervals (fun interval member => by
        rw [rejected interval member]
        rfl)
    rw [sum_zero] at empty
    change partition.touchLength point = 0 at empty
    rw [empty]
    exact nonnegative

/-- Overlapping exceptional marks are charged at most once per original cell.

Each single point costs at most twice the mesh radius. Summing over the
retained finite point list bounds the union of marked cells, including
repeated points, overlaps and endpoints. -/
theorem markedLength_le (partition : Normalized) (points : List Fraction.Rational) (radius : Fraction.Rational)
    (positive : 0 < radius) (small : ∀ interval ∈ partition.intervals, interval.signedLength < radius) :
    partition.markedLength points ≤ (points.length : Fraction.Rational) * (radius + radius) := by
  have each : ∀ interval ∈ partition.intervals,
      (if interval.marked points then interval.signedLength else 0) ≤
        (points.map (fun point => if interval.touches point then interval.signedLength else 0)).sum := by
    intro interval member
    exact any_indicator_le points interval.touches interval.signedLength
      (Partition.Interval.signedLength_pos (partition.valid interval member)).le
  have unionBound := sum_le (fun interval => if interval.marked points then interval.signedLength else 0)
    (fun interval => (points.map (fun point => if interval.touches point then interval.signedLength else 0)).sum)
    partition.intervals each
  have pointBound := Purelib.Data.List.Rat.sum_map_le_length_mul_of_bounded points partition.touchLength
    (radius + radius) (fun point _ => partition.touchLength_le point radius positive small)
  calc
    partition.markedLength points ≤
        (partition.intervals.map (fun interval =>
          (points.map (fun point => if interval.touches point then interval.signedLength else 0)).sum)).sum :=
      unionBound
    _ = (points.map partition.touchLength).sum :=
      sum_swap (fun point interval => if interval.touches point then interval.signedLength else 0)
        points partition.intervals
    _ ≤ (points.length : Fraction.Rational) * (radius + radius) := pointBound

end Purelib.Integration.Partition.Unit.Normalized

end
