module
public import Purelib.Integration.Cell.Numerical.Common.Weights
public import Purelib.Data.Rat.Interval.Intersection
import Purelib.Data.List.Map

/-!
# Intersections of numerical common refinements

Each child intersects the two original parent ranges using the overlap forced
by their numerical admission. Its cached left point state is retained, and
the resulting range overlaps every original finite point state on that child.
-/

public section

namespace Purelib.Integration.NumericalFrontier.CommonReading

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Intersect the actual two original parent ranges at this common child. -/
@[expose] def intersectionRange {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request) :
    Purelib.Data.Rat.Interval := reading.leftCell.val.range.intersect reading.rightCell.val.range reading.ranges_overlap

/-- Construct a common child retaining its actual cached left numerical point state. -/
@[expose] def intersectionCell {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest}
    (reading : CommonReading left right request) : IntegrationCell (NumericalPoint source) :=
  let bound := reading.intersectionRange
  { item := reading.leftPoint
    weight := reading.entry.child.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos reading.valid).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- The cached common left point retains the exact original child domain. -/
theorem intersectionCell_domain {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.intersectionCell.item.interval = reading.entry.child := by
  change reading.leftPoint.interval = reading.entry.child
  rw [reading.left_point_eq]
  rfl

/-- The intersection overlaps every finite point state throughout its original child. -/
theorem intersectionCell_source_overlap {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request)
    (point : Fraction.Rational) (lower : reading.entry.child.start ≤ point)
    (upper : point ≤ reading.entry.child.finish) (state : (source point).State) :
    reading.intersectionCell.lower ≤ ((source point).bound state).upper ∧
      ((source point).bound state).lower ≤ reading.intersectionCell.upper := by
  have leftMember := Purelib.Data.List.mem_of_getElem? left.cells reading.entry.leftOwner.index reading.leftCell.val
    reading.leftCell.property.1
  have rightMember := Purelib.Data.List.mem_of_getElem? right.cells reading.entry.rightOwner.index reading.rightCell.val
    reading.rightCell.property.1
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
  have leftOverlap := left.source_overlap reading.leftCell.val leftMember point leftStart leftFinish state
  have rightOverlap := right.source_overlap reading.rightCell.val rightMember point rightStart rightFinish state
  change reading.intersectionRange.Overlaps ((source point).bound state)
  exact Interval.intersect_overlaps reading.leftCell.val.range reading.rightCell.val.range
    ((source point).bound state) reading.ranges_overlap leftOverlap rightOverlap

end Purelib.Integration.NumericalFrontier.CommonReading

namespace Purelib.Integration.NumericalFrontier.CommonReadings

open Purelib.Approximation
open Purelib.Data.Rat

/-- Intersect the two actual numerical parent ranges on each original common child. -/
@[expose] def intersection {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest}
    (common : CommonReadings left right request) : NumericalFrontier source := by
  let cells := common.readings.map CommonReading.intersectionCell
  exact
    { partition := common.refinement.partition
      cells := cells
      domains_eq := by
        change (common.readings.map CommonReading.intersectionCell).map (fun cell => cell.item.interval) = _
        rw [Purelib.Data.List.Map.map_map]
        calc
          _ = common.readings.map (fun reading => reading.entry.child) := by
            apply Purelib.Data.List.Map.map_congr_left
            intro reading _
            exact reading.intersectionCell_domain
          _ = common.refinement.partition.intervals := common.reading_domains
      weight_eq := by
        intro cell member
        change cell ∈ common.readings.map CommonReading.intersectionCell at member
        obtain ⟨reading, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
        cases equal
        rw [reading.intersectionCell_domain]
        rfl
      source_overlap := by
        intro cell member point lower upper state
        change cell ∈ common.readings.map CommonReading.intersectionCell at member
        obtain ⟨reading, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
        cases equal
        rw [reading.intersectionCell_domain] at lower upper
        exact reading.intersectionCell_source_overlap point lower upper state }

/-- The intersected numerical integral enclosure refines the original left enclosure. -/
theorem intersection_refines_left {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (common : CommonReadings left right request) :
    Purelib.Data.Rat.Interval.Refines (integralBound common.intersection.cells) (integralBound left.cells) := by
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
    have refines := Interval.intersect_refines_left reading.leftCell.val.range reading.rightCell.val.range
      reading.ranges_overlap
    exact ⟨refines.lower, refines.upper⟩

/-- The intersected numerical integral enclosure refines the original right enclosure. -/
theorem intersection_refines_right {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (common : CommonReadings left right request) :
    Purelib.Data.Rat.Interval.Refines (integralBound common.intersection.cells) (integralBound right.cells) := by
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
    have refines := Interval.intersect_refines_right reading.leftCell.val.range reading.rightCell.val.range
      reading.ranges_overlap
    exact ⟨refines.lower, refines.upper⟩

end Purelib.Integration.NumericalFrontier.CommonReadings

end
