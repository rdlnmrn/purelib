module
public import Purelib.Integration.Cell.Source.Comparison.Weights
public import Purelib.Data.Rat.Interval.Intersection
import Purelib.Data.List.Map
import Purelib.Data.List.Attach

/-!
# Source-preserving intersection of common cells

The actual common rational reading lies in both original parent ranges.
Intersecting those ranges on each retained child gives a new source frontier
whose integral enclosure refines both original frontier enclosures.
-/

public section

namespace Purelib.Integration.SourceFrontier.CommonReading

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- View the actual left parent cell's original value range as a rational interval. -/
@[expose] def leftRange {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) : Rat.Interval :=
  reading.leftCell.val.range

/-- View the actual right parent cell's original value range as a rational interval. -/
@[expose] def rightRange {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) : Rat.Interval :=
  reading.rightCell.val.range

/-- Both original parent ranges overlap at the actual shared rational source reading. -/
theorem ranges_overlap {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) :
    reading.leftRange.Overlaps reading.rightRange := by
  have same := reading.readings_eq (fun _ _ _ => rfl)
  have rightInside : reading.rightRange.Contains reading.leftReading := by
    rw [same]
    exact reading.right_inside
  exact Rat.Interval.overlaps_of_common reading.left_inside rightInside

/-- Intersect the two original parent ranges using their actual common source observation. -/
@[expose] def intersectionRange {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) : Rat.Interval :=
  reading.leftRange.intersect reading.rightRange reading.ranges_overlap

/-- Construct the retained child cell with intersected ranges and its original rational tag.

The child consumes the same saved left reading as the common comparison.
The right parent and its observation remain available in that comparison. -/
@[expose] def intersectionCell {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) : IntegrationCell (SourcePoint source) :=
  let bound := reading.intersectionRange
  { item := ⟨reading.entry.child, reading.tag, reading.tag_inside.1, reading.tag_inside.2, reading.leftReading,
      reading.left_reading_eq.trans (reading.leftCell.val.item.readAt_eq reading.tag)⟩
    weight := reading.entry.child.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos reading.valid).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- The intersection cell retains the actual left common reading at its selected tag. -/
theorem intersectionCell_reading {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) :
    reading.intersectionCell.item.reading = reading.leftReading := rfl

/-- The intersected range contains the original source at every rational point of the retained child. -/
theorem intersectionCell_source_range {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (reading : CommonReading left right) (point : Fraction.Rational)
    (lower : reading.entry.child.start ≤ point) (upper : point ≤ reading.entry.child.finish) :
    reading.intersectionCell.lower ≤ source point ∧ source point ≤ reading.intersectionCell.upper := by
  have leftMember := Purelib.Data.List.mem_of_getElem? left.cells reading.entry.leftOwner.index reading.leftCell.val
    reading.leftCell.property.1
  have rightMember := Purelib.Data.List.mem_of_getElem? right.cells reading.entry.rightOwner.index
    reading.rightCell.val reading.rightCell.property.1
  have leftStart : reading.leftCell.val.item.interval.start ≤ point := by
    rw [congrArg Partition.Interval.start reading.leftCell.property.2]
    exact reading.entry.leftOwner.start_le.trans lower
  have leftFinish : point ≤ reading.leftCell.val.item.interval.finish := by
    rw [congrArg Partition.Interval.finish reading.leftCell.property.2]
    exact upper.trans reading.entry.leftOwner.finish_le
  have rightStart : reading.rightCell.val.item.interval.start ≤ point := by
    rw [congrArg Partition.Interval.start reading.rightCell.property.2]
    exact reading.entry.rightOwner.start_le.trans lower
  have rightFinish : point ≤ reading.rightCell.val.item.interval.finish := by
    rw [congrArg Partition.Interval.finish reading.rightCell.property.2]
    exact upper.trans reading.entry.rightOwner.finish_le
  have leftInside := left.source_range reading.leftCell.val leftMember point leftStart leftFinish
  have rightInside := right.source_range reading.rightCell.val rightMember point rightStart rightFinish
  change reading.intersectionRange.Contains (source point)
  exact (Rat.Interval.intersect_contains_iff reading.leftRange reading.rightRange
    reading.ranges_overlap (source point)).mpr ⟨leftInside, rightInside⟩

end Purelib.Integration.SourceFrontier.CommonReading

namespace Purelib.Integration.SourceFrontier.CommonReadings

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Intersect the original source ranges on every actual common child.

The resulting frontier retains the original common partition and cached tags.
Its source laws follow from both parent range laws throughout each child. -/
@[expose] def intersection {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (common : CommonReadings left right) : SourceFrontier source := by
  let cells := common.readings.map CommonReading.intersectionCell
  exact
    { partition := common.refinement.partition
      cells := cells
      domains_eq := by
        change (common.readings.map CommonReading.intersectionCell).map (fun cell => cell.item.interval) = _
        rw [Purelib.Data.List.Map.map_map]
        exact common.reading_domains
      weight_eq := by
        intro cell member
        change cell ∈ common.readings.map CommonReading.intersectionCell at member
        rcases (Purelib.Data.List.Map.mem_map).mp member with ⟨reading, _, equal⟩
        cases equal
        rfl
      source_range := by
        intro cell member point lower upper
        change cell ∈ common.readings.map CommonReading.intersectionCell at member
        rcases (Purelib.Data.List.Map.mem_map).mp member with ⟨reading, _, equal⟩
        cases equal
        exact reading.intersectionCell_source_range point lower upper }

/-- The intersected frontier's integral enclosure refines its original left input. -/
theorem intersection_refines_left {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (common : CommonReadings left right) :
    Rat.Interval.Refines (integralBound common.intersection.cells) (integralBound left.cells) := by
  apply left.partitioned.redistributed_refines common.refinement.partition common.readings
    (fun reading => reading.entry.child) (fun reading => reading.leftCell.val) CommonReading.intersectionCell
    common.reading_domains
  · intro reading _
    exact ⟨reading.entry.leftOwner,
      Purelib.Data.List.mem_of_getElem? left.cells reading.entry.leftOwner.index reading.leftCell.val
        reading.leftCell.property.1, reading.leftCell.property.2⟩
  · intro reading _
    rfl
  · intro reading _
    have refines := Rat.Interval.intersect_refines_left
      reading.leftRange reading.rightRange reading.ranges_overlap
    exact ⟨refines.lower, refines.upper⟩

/-- The intersected frontier's integral enclosure refines its original right input. -/
theorem intersection_refines_right {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (common : CommonReadings left right) :
    Rat.Interval.Refines (integralBound common.intersection.cells) (integralBound right.cells) := by
  apply right.partitioned.redistributed_refines common.refinement.partition common.readings
    (fun reading => reading.entry.child) (fun reading => reading.rightCell.val) CommonReading.intersectionCell
    common.reading_domains
  · intro reading _
    exact ⟨reading.entry.rightOwner,
      Purelib.Data.List.mem_of_getElem? right.cells reading.entry.rightOwner.index reading.rightCell.val
        reading.rightCell.property.1, reading.rightCell.property.2⟩
  · intro reading _
    rfl
  · intro reading _
    have refines := Rat.Interval.intersect_refines_right
      reading.leftRange reading.rightRange reading.ranges_overlap
    exact ⟨refines.lower, refines.upper⟩

end Purelib.Integration.SourceFrontier.CommonReadings

end
