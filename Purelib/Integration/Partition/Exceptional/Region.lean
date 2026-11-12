module
public import Purelib.Integration.Partition.Exceptional
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Rat.Sum
import Purelib.Data.List.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Finite exceptional regions

Closed rational regions mark their intersecting cells of the retained unit
partition. A marked cell is charged once even when several regions overlap.
The length estimate uses a clipped mesh expansion of each original region.
-/

public section

namespace Purelib.Integration.Partition.Interval

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Decide whether two closed intervals intersect by their endpoint comparisons. -/
@[expose] def intersects (interval region : Interval) : Bool :=
  decide (interval.start ≤ region.finish ∧ region.start ≤ interval.finish)

/-- Intersection preserves both original endpoint comparisons. -/
theorem intersects_iff (interval region : Interval) :
    interval.intersects region = true ↔ interval.start ≤ region.finish ∧ region.start ≤ interval.finish := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- Mark a cell meeting at least one of the retained closed regions. -/
@[expose] def regionMarked (interval : Interval) (regions : List Interval) : Bool :=
  regions.any interval.intersects

/-- A marked cell meets an actual region in the original list. -/
theorem regionMarked_iff (interval : Interval) (regions : List Interval) :
    interval.regionMarked regions = true ↔
      ∃ region ∈ regions, interval.start ≤ region.finish ∧ region.start ≤ interval.finish := by
  constructor
  · intro marked
    obtain ⟨region, member, intersects⟩ := (Purelib.Data.List.Search.any_iff interval.intersects regions).mp marked
    exact ⟨region, member, (interval.intersects_iff region).mp intersects⟩
  · rintro ⟨region, member, intersects⟩
    exact (Purelib.Data.List.Search.any_iff interval.intersects regions).mpr
      ⟨region, member, (interval.intersects_iff region).mpr intersects⟩

/-- A cell containing a point of a retained region is marked. -/
theorem regionMarked_of_point (interval : Interval) (regions : List Interval) (region : Interval)
    (member : region ∈ regions) (point : Fraction.Rational)
    (cellLower : interval.start ≤ point) (cellUpper : point ≤ interval.finish)
    (regionLower : region.start ≤ point) (regionUpper : point ≤ region.finish) :
    interval.regionMarked regions = true :=
  (interval.regionMarked_iff regions).mpr ⟨region, member, cellLower.trans regionUpper, regionLower.trans cellUpper⟩

/-- Expand both endpoints by a rational radius and clip them to the unit interval. -/
@[expose] def regionExpansion (region : Interval) (radius : Fraction.Rational) : Interval :=
  let unit : Interval := ⟨0, 1⟩
  ⟨unit.clamp (region.start - radius), unit.clamp (region.finish + radius)⟩

/-- Expanding an ordered unit region by a nonnegative radius gives ordered unit endpoints. -/
theorem regionExpansion_bounds (region : Interval) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (ordered : region.start ≤ region.finish) :
    0 ≤ (region.regionExpansion radius).start ∧
      (region.regionExpansion radius).start ≤ (region.regionExpansion radius).finish ∧
        (region.regionExpansion radius).finish ≤ 1 := by
  let unit : Interval := ⟨0, 1⟩
  have unitOrdered : unit.start ≤ unit.finish := by decide
  have neg := Arithmetic.neg_le_neg_direct nonnegative
  rw [neg_zero] at neg
  have before := Arithmetic.add_le_add_right_direct neg region.start
  have beforeEq : -radius + region.start = region.start - radius := by ring1
  rw [beforeEq, Fraction.Field.zero_add] at before
  have after := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl region.finish) nonnegative
  have afterEq : region.finish + 0 = region.finish := by ring1
  rw [afterEq] at after
  exact ⟨(unit.clamp_bounds unitOrdered (region.start - radius)).1,
    unit.clamp_mono (before.trans (ordered.trans after)),
    (unit.clamp_bounds unitOrdered (region.finish + radius)).2⟩

/-- Expanding a unit region increases its length by at most twice the radius. -/
theorem regionExpansion_length_le (region : Interval) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (lower : 0 ≤ region.start) (ordered : region.start ≤ region.finish) (upper : region.finish ≤ 1) :
    (region.regionExpansion radius).signedLength ≤ region.signedLength + (radius + radius) := by
  let unit : Interval := ⟨0, 1⟩
  have negative := Arithmetic.neg_le_neg_direct nonnegative
  rw [neg_zero] at negative
  have shifted := Arithmetic.add_le_add_right_direct negative region.start
  have identity : -radius + region.start = region.start - radius := by ring1
  rw [identity, Fraction.Field.zero_add] at shifted
  have subLeOne := shifted.trans (ordered.trans upper)
  have addNonnegative := Arithmetic.add_le_add_direct (lower.trans ordered) nonnegative
  change (0 : Fraction.Rational) ≤ region.finish + radius at addNonnegative
  have lowerClamp : region.start - radius ≤ unit.clamp (region.start - radius) := by
    change region.start - radius ≤ max 0 (min 1 (region.start - radius))
    rw [Fraction.Order.Basic.min_eq_right subLeOne]
    exact Fraction.Order.Basic.le_max_right _ _
  have upperClamp : unit.clamp (region.finish + radius) ≤ region.finish + radius := by
    change max 0 (min 1 (region.finish + radius)) ≤ region.finish + radius
    exact Fraction.Order.Basic.max_le addNonnegative (Fraction.Order.Basic.min_le_right _ _)
  have bound := Arithmetic.sub_le_sub_direct upperClamp lowerClamp
  have width : (region.finish + radius) - (region.start - radius) =
      region.signedLength + (radius + radius) := by dsimp [signedLength]; ring1
  rw [width] at bound
  exact bound

/-- A short unit cell meeting a region lies within that region's clipped expansion. -/
theorem regionExpansion_contains_child (region : Interval) (radius : Fraction.Rational) (child : Interval)
    (valid : child.Valid) (inside : child.start ≤ region.finish ∧ region.start ≤ child.finish)
    (small : child.signedLength < radius) :
    (region.regionExpansion radius).start ≤ child.start ∧ child.finish ≤ (region.regionExpansion radius).finish := by
  let unit : Interval := ⟨0, 1⟩
  have firstDistance : region.start - child.start ≤ child.signedLength :=
    Arithmetic.sub_le_sub_direct inside.2 (Fraction.Order.Basic.le_refl _)
  have secondDistance : child.finish - region.finish ≤ child.signedLength :=
    Arithmetic.sub_le_sub_direct (Fraction.Order.Basic.le_refl _) inside.1
  have firstBound := firstDistance.trans small.le
  have secondBound := secondDistance.trans small.le
  have firstAdded := Arithmetic.sub_le_iff_le_add_direct.mp firstBound
  have firstCommute : radius + child.start = child.start + radius := by ring1
  rw [firstCommute] at firstAdded
  have before : region.start - radius ≤ child.start := Arithmetic.sub_le_iff_le_add_direct.mpr firstAdded
  have after := Arithmetic.sub_le_iff_le_add_direct.mp secondBound
  have secondCommute : radius + region.finish = region.finish + radius := by ring1
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

/-- Sum the lengths of the actual cells meeting one retained closed region. -/
@[expose] def regionLength (partition : Normalized) (region : Interval) : Fraction.Rational :=
  (partition.intervals.map (fun interval => if interval.intersects region then interval.signedLength else 0)).sum

/-- Sum the lengths of cells meeting any retained region, charging each cell once. -/
@[expose] def regionsLength (partition : Normalized) (regions : List Interval) : Fraction.Rational :=
  (partition.intervals.map (fun interval => if interval.regionMarked regions then interval.signedLength else 0)).sum

/-- The cells meeting a unit region fit inside its clipped mesh expansion. -/
theorem regionLength_le (partition : Normalized) (region : Interval) (radius : Fraction.Rational)
    (bounds : 0 ≤ region.start ∧ region.start ≤ region.finish ∧ region.finish ≤ 1) (positive : 0 < radius)
    (small : ∀ interval ∈ partition.intervals, interval.signedLength < radius) :
    partition.regionLength region ≤ region.signedLength + (radius + radius) := by
  let cover := region.regionExpansion radius
  have validCover := region.regionExpansion_bounds radius positive.le bounds.2.1
  have each : ∀ interval ∈ partition.intervals,
      (if interval.intersects region then interval.signedLength else 0) ≤ cover.clampedLength interval := by
    intro interval member
    have valid := partition.valid interval member
    cases accepted : interval.intersects region with
    | false =>
        change (0 : Fraction.Rational) ≤ cover.clampedLength interval
        exact cover.clampedLength_nonnegative interval valid.2.1.le
    | true =>
        change interval.signedLength ≤ cover.clampedLength interval
        have inside := (interval.intersects_iff region).mp accepted
        have located := region.regionExpansion_contains_child radius interval valid inside (small interval member)
        have equal := cover.clamp_child_length interval located.1 valid.2.1.le located.2
        change cover.clampedLength interval = interval.signedLength at equal
        rewrite [equal]
        exact Fraction.Order.Basic.le_refl _
  have sumBound := sum_le (fun interval => if interval.intersects region then interval.signedLength else 0)
    (fun interval => cover.clampedLength interval) partition.intervals each
  have total := partition.clampedLength_sum_of_bounds cover validCover.1 validCover.2.1 validCover.2.2
  rw [total] at sumBound
  exact sumBound.trans (region.regionExpansion_length_le radius positive.le bounds.1 bounds.2.1 bounds.2.2)

/-- The actual union of marked cells costs no more than the sum of the individual expanded-region lengths.

The left side charges overlapping regions only once per original cell. The
right side conservatively sums the exact retained region lengths and each
mesh expansion, including duplicates and shared endpoints. -/
theorem regionsLength_le (partition : Normalized) (regions : List Interval) (radius : Fraction.Rational)
    (bounds : ∀ region ∈ regions, 0 ≤ region.start ∧ region.start ≤ region.finish ∧ region.finish ≤ 1)
    (positive : 0 < radius) (small : ∀ interval ∈ partition.intervals, interval.signedLength < radius) :
    partition.regionsLength regions ≤
      (regions.map (fun region => region.signedLength + (radius + radius))).sum := by
  have each : ∀ interval ∈ partition.intervals,
      (if interval.regionMarked regions then interval.signedLength else 0) ≤
        (regions.map (fun region => if interval.intersects region then interval.signedLength else 0)).sum := by
    intro interval member
    exact any_indicator_le regions interval.intersects interval.signedLength
      (Interval.signedLength_pos (partition.valid interval member)).le
  have unionBound := sum_le (fun interval => if interval.regionMarked regions then interval.signedLength else 0)
    (fun interval => (regions.map (fun region => if interval.intersects region then interval.signedLength else 0)).sum)
    partition.intervals each
  calc
    partition.regionsLength regions ≤
        (partition.intervals.map (fun interval =>
          (regions.map (fun region => if interval.intersects region then interval.signedLength else 0)).sum)).sum :=
      unionBound
    _ = (regions.map partition.regionLength).sum :=
      sum_swap (fun region interval => if interval.intersects region then interval.signedLength else 0)
        regions partition.intervals
    _ ≤ (regions.map (fun region => region.signedLength + (radius + radius))).sum :=
      sum_le _ _ regions (fun region member => partition.regionLength_le region radius (bounds region member)
        positive small)

/-- The marked-cell union is bounded by the total region lengths and their finite mesh-expansion budget. -/
theorem regionsLength_le_total (partition : Normalized) (regions : List Interval) (radius : Fraction.Rational)
    (bounds : ∀ region ∈ regions, 0 ≤ region.start ∧ region.start ≤ region.finish ∧ region.finish ≤ 1)
    (positive : 0 < radius) (small : ∀ interval ∈ partition.intervals, interval.signedLength < radius) :
    partition.regionsLength regions ≤ (regions.map Interval.signedLength).sum +
      (regions.length : Fraction.Rational) * (radius + radius) := by
  have unionBound := partition.regionsLength_le regions radius bounds positive small
  have split := sum_add Interval.signedLength (fun _ => radius + radius) regions
  rw [split] at unionBound
  have countBound := Purelib.Data.List.Rat.sum_map_le_length_mul_of_bounded regions
    (fun _ => radius + radius) (radius + radius) (fun _ _ => Fraction.Order.Basic.le_refl _)
  exact unionBound.trans (Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl _) countBound)

end Purelib.Integration.Partition.Unit.Normalized

end
