module
public import Purelib.Integration.Cell.Numerical.Comparison
import Purelib.Data.List.GetD
import Purelib.Data.List.Map
import Purelib.Data.List.Attach
import Purelib.Data.List.Pairwise
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Common rational tags for numerical source frontiers

Each common child keeps both original indexed parents and the actual point
observations at the same rational tag. Independent sources retain separate
states; one source can reuse a shared saved observation. The resulting
intervals and their rational overlap witnesses remain attached to the child.
-/

public section

namespace Purelib.Integration.NumericalFrontier

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- Two actual numerical requests at one common child of the original frontiers.

The indexed owners select the original left and right cells. Both numerical
points use the same rational tag and meet the requested width, retaining
their selected original states, requests and interval readbacks. Each original
cell range overlaps its corresponding actual point interval. -/
structure CommonReading {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) where
  /-- The original common child and its two indexed parent owners. -/ entry :
    Unit.Common.CommonEntry left.partition right.partition
  /-- The common child is a valid positive-length unit interval. -/ valid : entry.child.Valid
  /-- The common rational query tag. -/ tag : Fraction.Rational
  /-- The tag lies in the original closed common child. -/ tag_inside :
    entry.child.start ≤ tag ∧ tag ≤ entry.child.finish
  /-- The actual left cell at its retained original parent index. -/ leftCell :
    {cell : IntegrationCell (NumericalPoint leftSource) //
      Purelib.Data.List.getElem? left.cells entry.leftOwner.index = some cell ∧
        cell.item.interval = entry.leftOwner.parent}
  /-- The actual right cell at its retained original parent index. -/ rightCell :
    {cell : IntegrationCell (NumericalPoint rightSource) //
      Purelib.Data.List.getElem? right.cells entry.rightOwner.index = some cell ∧
        cell.item.interval = entry.rightOwner.parent}
  /-- The actual left point-process request and cached interval. -/ leftPoint : NumericalPoint leftSource
  /-- The original left point whose state supplies the common-tag observation. -/ leftOrigin : NumericalPoint leftSource
  /-- The left observation uses its original selected point and state. -/ left_point_eq :
    leftPoint = leftOrigin.retag entry.child tag tag_inside.1 tag_inside.2 request
  /-- The actual right point-process request and cached interval. -/ rightPoint : NumericalPoint rightSource
  /-- The original right point whose state supplies the common-tag observation. -/ rightOrigin :
    NumericalPoint rightSource
  /-- The right observation uses its original selected point and state. -/ right_point_eq :
    rightPoint = rightOrigin.retag entry.child tag tag_inside.1 tag_inside.2 request
  /-- The original left range overlaps the actual left point interval. -/ left_overlap :
    leftCell.val.range.Overlaps leftPoint.reading
  /-- The original right range overlaps the actual right point interval. -/ right_overlap :
    rightCell.val.range.Overlaps rightPoint.reading

constructive_injectivity CommonReading

set_option genInjectivity false in
/-- Two actual point observations and their selected original state owners at one common tag. -/
structure PointPair (leftSource rightSource : Fraction.Rational → BoundProcess) (interval : Partition.Interval)
    (tag : Fraction.Rational) (tagInside : interval.start ≤ tag ∧ tag ≤ interval.finish)
    (request : AccuracyRequest) where
  /-- The selected left point state before the displayed retag. -/ leftOrigin : NumericalPoint leftSource
  /-- The actual left observation. -/ leftPoint : NumericalPoint leftSource
  /-- The left observation is the displayed retag of its selected original point. -/ left_eq :
    leftPoint = leftOrigin.retag interval tag tagInside.1 tagInside.2 request
  /-- The selected right point state before the displayed retag. -/ rightOrigin : NumericalPoint rightSource
  /-- The actual right observation. -/ rightPoint : NumericalPoint rightSource
  /-- The right observation is the displayed retag of its selected original point. -/ right_eq :
    rightPoint = rightOrigin.retag interval tag tagInside.1 tagInside.2 request

constructive_injectivity PointPair

/-- Make the two original independent parent-point observations. -/
@[expose] def independentPair {leftSource rightSource : Fraction.Rational → BoundProcess}
    (interval : Partition.Interval) (_valid : interval.Valid) (tag : Fraction.Rational)
    (tagInside : interval.start ≤ tag ∧ tag ≤ interval.finish) (request : AccuracyRequest)
    (left : NumericalPoint leftSource) (right : NumericalPoint rightSource) :
    PointPair leftSource rightSource interval tag tagInside request :=
  ⟨left, left.retag interval tag tagInside.1 tagInside.2 request, rfl,
    right, right.retag interval tag tagInside.1 tagInside.2 request, rfl⟩

/-- Make both sides of a common child from one returned numerical observation. -/
@[expose] def pairFromObservation {source : Fraction.Rational → BoundProcess}
    (interval : Partition.Interval) (tag : Fraction.Rational)
    (tagInside : interval.start ≤ tag ∧ tag ≤ interval.finish) (request : AccuracyRequest)
    (selected : NumericalPoint.Observation source interval tag request) :
    PointPair source source interval tag tagInside request := by
  let original := selected.val
  have same : tag = original.point := selected.property.2.1.symm
  let point := original.move interval tag tagInside.1 tagInside.2 same
  have point_eq : point = original.retag interval tag tagInside.1 tagInside.2 request :=
    (original.retag_reused_of_eq interval tag tagInside.1 tagInside.2 request same selected.property.2.2).symm
  exact ⟨original, point, point_eq, original, point, point_eq⟩

/-- Select one actual observation from a common source bank and retain it on both sides. -/
@[expose] def cachedPair {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (interval : Partition.Interval) (_valid : interval.Valid) (tag : Fraction.Rational)
    (tagInside : interval.start ≤ tag ∧ tag ≤ interval.finish) (request : AccuracyRequest)
    (_left _right : NumericalPoint source) : PointPair source source interval tag tagInside request :=
  pairFromObservation interval tag tagInside request
    (NumericalPoint.atCached source cached interval tag tagInside.1 tagInside.2 request)

/-- Both sides of a cache-selected pair retain the very same numerical observation. -/
theorem cachedPair_points_eq {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (interval : Partition.Interval) (valid : interval.Valid) (tag : Fraction.Rational)
    (tagInside : interval.start ≤ tag ∧ tag ≤ interval.finish) (request : AccuracyRequest)
    (left right : NumericalPoint source) :
    (cachedPair cached interval valid tag tagInside request left right).leftPoint =
      (cachedPair cached interval valid tag tagInside request left right).rightPoint := rfl

/-- Assemble an indexed common child from the actual returned numerical point pair. -/
@[expose] def readCommonFromPair {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish)
    (pair : PointPair leftSource rightSource entry.child tag tagInside request) :
    CommonReading left right request := by
  let leftCell := left.partitioned.cellAtOwner entry.leftOwner
  let rightCell := right.partitioned.cellAtOwner entry.rightOwner
  have leftMember : leftCell.val ∈ left.cells :=
    Purelib.Data.List.mem_of_getElem? left.cells entry.leftOwner.index leftCell.val leftCell.property.1
  have rightMember : rightCell.val ∈ right.cells :=
    Purelib.Data.List.mem_of_getElem? right.cells entry.rightOwner.index rightCell.val rightCell.property.1
  have leftStart : leftCell.val.item.interval.start ≤ tag := by
    have equal := congrArg Partition.Interval.start leftCell.property.2
    rw [equal]
    exact entry.leftOwner.start_le.trans tagInside.1
  have leftFinish : tag ≤ leftCell.val.item.interval.finish := by
    have equal := congrArg Partition.Interval.finish leftCell.property.2
    rw [equal]
    exact tagInside.2.trans entry.leftOwner.finish_le
  have rightStart : rightCell.val.item.interval.start ≤ tag := by
    have equal := congrArg Partition.Interval.start rightCell.property.2
    rw [equal]
    exact entry.rightOwner.start_le.trans tagInside.1
  have rightFinish : tag ≤ rightCell.val.item.interval.finish := by
    have equal := congrArg Partition.Interval.finish rightCell.property.2
    rw [equal]
    exact tagInside.2.trans entry.rightOwner.finish_le
  let leftPoint := pair.leftPoint
  let rightPoint := pair.rightPoint
  have leftOverlap : leftCell.val.range.Overlaps leftPoint.reading := by
    rw [leftPoint.reading_eq]
    change leftCell.val.range.Overlaps ((leftSource pair.leftPoint.point).bound pair.leftPoint.state)
    rw [pair.left_eq]
    exact left.source_overlap leftCell.val leftMember tag leftStart leftFinish
      (pair.leftOrigin.retag entry.child tag tagInside.1 tagInside.2 request).state
  have rightOverlap : rightCell.val.range.Overlaps rightPoint.reading := by
    rw [rightPoint.reading_eq]
    change rightCell.val.range.Overlaps ((rightSource pair.rightPoint.point).bound pair.rightPoint.state)
    rw [pair.right_eq]
    exact right.source_overlap rightCell.val rightMember tag rightStart rightFinish
      (pair.rightOrigin.retag entry.child tag tagInside.1 tagInside.2 request).state
  exact
    { entry := entry
      valid := valid
      tag := tag
      tag_inside := tagInside
      leftCell := leftCell
      rightCell := rightCell
      leftPoint := leftPoint
      leftOrigin := pair.leftOrigin
      left_point_eq := pair.left_eq
      rightPoint := rightPoint
      rightOrigin := pair.rightOrigin
      right_point_eq := pair.right_eq
      left_overlap := leftOverlap
      right_overlap := rightOverlap }

/-- Make two actual requests at a rational tag in an indexed common child. -/
@[expose] def readCommonWith {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish)
    (reader : NumericalPoint leftSource → NumericalPoint rightSource →
      PointPair leftSource rightSource entry.child tag tagInside request) :
    CommonReading left right request :=
  readCommonFromPair left right request entry valid tag tagInside
    (reader (left.partitioned.cellAtOwner entry.leftOwner).val.item
      (right.partitioned.cellAtOwner entry.rightOwner).val.item)

/-- Make the two independent parent-point requests at a rational common tag. -/
@[expose] def readCommon {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish) :
    CommonReading left right request :=
  readCommonWith left right request entry valid tag tagInside
    (independentPair entry.child valid tag tagInside request)

namespace CommonReading

/-- The common tag belongs to the actual original left parent cell. -/
theorem left_tag_inside {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.leftCell.val.item.interval.start ≤ reading.tag ∧
      reading.tag ≤ reading.leftCell.val.item.interval.finish := by
  constructor
  · have equal := congrArg Partition.Interval.start reading.leftCell.property.2
    rw [equal]
    exact reading.entry.leftOwner.start_le.trans reading.tag_inside.1
  · have equal := congrArg Partition.Interval.finish reading.leftCell.property.2
    rw [equal]
    exact reading.tag_inside.2.trans reading.entry.leftOwner.finish_le

/-- The common tag belongs to the actual original right parent cell. -/
theorem right_tag_inside {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.rightCell.val.item.interval.start ≤ reading.tag ∧
      reading.tag ≤ reading.rightCell.val.item.interval.finish := by
  constructor
  · have equal := congrArg Partition.Interval.start reading.rightCell.property.2
    rw [equal]
    exact reading.entry.rightOwner.start_le.trans reading.tag_inside.1
  · have equal := congrArg Partition.Interval.finish reading.rightCell.property.2
    rw [equal]
    exact reading.tag_inside.2.trans reading.entry.rightOwner.finish_le

/-- The two original parent ranges overlap, as forced by their joint numerical admission. -/
theorem ranges_overlap {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.leftCell.val.range.Overlaps reading.rightCell.val.range := by
  have leftMember := Purelib.Data.List.mem_of_getElem? left.cells reading.entry.leftOwner.index reading.leftCell.val
    reading.leftCell.property.1
  have rightMember := Purelib.Data.List.mem_of_getElem? right.cells reading.entry.rightOwner.index reading.rightCell.val
    reading.rightCell.property.1
  exact left.cell_ranges_overlap_at right reading.leftCell.val reading.rightCell.val leftMember rightMember
    reading.tag reading.left_tag_inside reading.right_tag_inside

/-- Select the rational overlap witness in the actual left cell and point intervals. -/
@[expose] def leftReading {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest}
    (reading : CommonReading left right request) : Fraction.Rational :=
  reading.leftCell.val.range.overlapWitness reading.leftPoint.reading

/-- Select the rational overlap witness in the actual right cell and point intervals. -/
@[expose] def rightReading {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest}
    (reading : CommonReading left right request) : Fraction.Rational :=
  reading.rightCell.val.range.overlapWitness reading.rightPoint.reading

/-- The actual absolute discrepancy of the two retained common-point witnesses. -/
@[expose] def discrepancy {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest}
    (reading : CommonReading left right request) : Fraction.Rational :=
  Fraction.abs (reading.leftReading - reading.rightReading)

/-- The computed left reading belongs to both its original cell range and point interval. -/
theorem left_inside {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.leftCell.val.range.Contains reading.leftReading ∧ reading.leftPoint.reading.Contains reading.leftReading :=
  Interval.overlapWitness_inside reading.left_overlap

/-- The computed right reading belongs to both its original cell range and point interval. -/
theorem right_inside {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.rightCell.val.range.Contains reading.rightReading ∧
      reading.rightPoint.reading.Contains reading.rightReading :=
  Interval.overlapWitness_inside reading.right_overlap

/-- The saved left point request overlaps any state of its coherent original point process. -/
theorem leftPoint_overlaps {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request)
    (coherent : (leftSource reading.tag).Coherent) (state : (leftSource reading.tag).State) :
    reading.leftPoint.reading.Overlaps ((leftSource reading.tag).bound state) := by
  rw [reading.left_point_eq]
  rw [NumericalPoint.reading_eq]
  change ((leftSource reading.tag).bound _).Overlaps ((leftSource reading.tag).bound state)
  exact coherent _ state

/-- The saved right point request overlaps any state of its coherent original point process. -/
theorem rightPoint_overlaps {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request)
    (coherent : (rightSource reading.tag).Coherent) (state : (rightSource reading.tag).State) :
    reading.rightPoint.reading.Overlaps ((rightSource reading.tag).bound state) := by
  rw [reading.right_point_eq]
  rw [NumericalPoint.reading_eq]
  change ((rightSource reading.tag).bound _).Overlaps ((rightSource reading.tag).bound state)
  exact coherent _ state

/-- The two actual point intervals overlap when their original point process is coherent. -/
theorem point_overlaps {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request)
    (coherent : (source reading.tag).Coherent) : reading.leftPoint.reading.Overlaps reading.rightPoint.reading := by
  rw [reading.left_point_eq, reading.right_point_eq]
  rw [NumericalPoint.reading_eq, NumericalPoint.reading_eq]
  change ((source reading.tag).bound _).Overlaps ((source reading.tag).bound _)
  exact coherent _ _

/-- The actual common readings differ by at most their two requested point widths. -/
theorem reading_difference_le {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request)
    (coherent : (source reading.tag).Coherent) :
    Fraction.abs (reading.leftReading - reading.rightReading) ≤
      reading.leftPoint.reading.width + reading.rightPoint.reading.width :=
  Interval.abs_sub_le_of_overlaps reading.left_inside.2 reading.right_inside.2 (reading.point_overlaps coherent)

/-- The actual left point interval meets the retained common request. -/
theorem left_width_lt {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.leftPoint.reading.width < request.tolerance := by
  rw [reading.left_point_eq]
  exact reading.leftOrigin.retag_reading_width_lt reading.entry.child reading.tag
    reading.tag_inside.1 reading.tag_inside.2 request

/-- The actual right point interval meets the retained common request. -/
theorem right_width_lt {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) :
    reading.rightPoint.reading.width < request.tolerance := by
  rw [reading.right_point_eq]
  exact reading.rightOrigin.retag_reading_width_lt reading.entry.child reading.tag
    reading.tag_inside.1 reading.tag_inside.2 request

/-- Coherent point states pay for both actual common readings using the retained request. -/
theorem reading_difference_le_request {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (reading : CommonReading left right request)
    (coherent : (source reading.tag).Coherent) :
    Fraction.abs (reading.leftReading - reading.rightReading) ≤ request.tolerance + request.tolerance :=
  (reading.reading_difference_le coherent).trans
    (Fraction.Order.Arithmetic.add_le_add_direct reading.left_width_lt.le reading.right_width_lt.le)

/-- Give a retained common reading its exact original child weight. -/
@[expose] def exactCell {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest}
    (reading : CommonReading left right request) : IntegrationCell (CommonReading left right request) :=
  IntegrationCell.exact reading reading.entry.child.signedLength reading.leftReading
    (Partition.Interval.signedLength_pos reading.valid).le

end CommonReading

set_option genInjectivity false in
/-- The actual point requests on every ordered child of one retained common refinement. -/
structure CommonReadings {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) where
  /-- The original common partition with both indexed parent owners. -/ refinement :
    Unit.Common.CommonRefinement left.partition right.partition
  /-- The actual numerical observations for each original common child. -/ readings :
    List (CommonReading left right request)
  /-- Reading the retained entries returns the common refinement's original ordered entries. -/ entries_eq :
    readings.map CommonReading.entry = refinement.entries

constructive_injectivity CommonReadings

/-- Common-reading collections with the same refinement and ordered observations are equal. -/
theorem CommonReadings.ext {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (first second : CommonReadings left right request) (refinement_eq : first.refinement = second.refinement)
    (readings_eq : first.readings = second.readings) : first = second := by
  cases first with
  | mk firstRefinement firstReadings firstEntries =>
    cases second with
    | mk secondRefinement secondReadings secondEntries =>
      cases refinement_eq
      cases readings_eq
      rfl

/-- Make the supplied point observations at tags on a retained common partition. -/
@[expose] def readRefinementWith {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (tag : Partition.Interval → Fraction.Rational)
    (tagInside : ∀ interval, interval.Valid → interval.start ≤ tag interval ∧ tag interval ≤ interval.finish)
    (reader : (interval : Partition.Interval) → (valid : interval.Valid) →
      (point : Fraction.Rational) → (inside : interval.start ≤ point ∧ point ≤ interval.finish) →
      NumericalPoint leftSource → NumericalPoint rightSource → PointPair leftSource rightSource interval point inside
        request) :
    CommonReadings left right request := by
  let readings : List (CommonReading left right request) := refinement.entries.attach.map fun
      (entry : {entry // entry ∈ refinement.entries}) =>
    let valid : entry.val.child.Valid := by
      have childMember : entry.val.child ∈ refinement.partition.intervals := by
        rw [← refinement.children_eq]
        exact (Purelib.Data.List.Map.mem_map).mpr ⟨entry.val, entry.property, rfl⟩
      exact refinement.partition.valid entry.val.child childMember
    readCommonWith left right request entry.val valid (tag entry.val.child) (tagInside entry.val.child valid)
      (reader entry.val.child valid (tag entry.val.child) (tagInside entry.val.child valid))
  exact
    { refinement := refinement
      readings := readings
      entries_eq := by
        change (refinement.entries.attach.map _).map CommonReading.entry = refinement.entries
        rw [Purelib.Data.List.Map.map_map]
        change refinement.entries.attach.map Subtype.val = refinement.entries
        exact Purelib.Data.List.attach_map_subtype_val _ }

/-- Make the original independent point requests at supplied tags on a retained common partition. -/
@[expose] def readRefinement {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (tag : Partition.Interval → Fraction.Rational)
    (tagInside : ∀ interval, interval.Valid → interval.start ≤ tag interval ∧ tag interval ≤ interval.finish) :
    CommonReadings left right request :=
  readRefinementWith left right request refinement tag tagInside
    (fun interval valid point inside => independentPair interval valid point inside request)

/-- Compute the common refinement and use the retained children's left endpoints as rational tags. -/
@[expose] def commonReadings {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource)
    (request : AccuracyRequest) : CommonReadings left right request :=
  readRefinement left right request (Unit.Common.commonRefinement left.partition right.partition)
    Partition.Interval.start (fun _ valid => ⟨le_rfl, valid.2.1.le⟩)

/-- Compute common readings of one source using one shared cached or continued observation per tag. -/
@[expose] def commonReadingsCached {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    CommonReadings left right request :=
  readRefinementWith left right request (Unit.Common.commonRefinement left.partition right.partition)
    Partition.Interval.start (fun _ valid => ⟨le_rfl, valid.2.1.le⟩)
    (fun interval valid point inside => cachedPair cached interval valid point inside request)

/-- Every cache-selected common child retains one shared numerical observation on both sides. -/
theorem commonReadingsCached_points_eq {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (reading : CommonReading left right request)
    (member : reading ∈ (commonReadingsCached left right cached request).readings) :
    reading.leftPoint = reading.rightPoint := by
  change reading ∈ (Unit.Common.commonRefinement left.partition right.partition).entries.attach.map _ at member
  obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  rfl

/-- Any readings of the original common refinement retain nondecreasing original left-parent indices. -/
theorem left_indices_of_common {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request)
    (refinement_eq : common.refinement = Unit.Common.commonRefinement left.partition right.partition) :
    common.readings.Pairwise (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index) := by
  have ordered : common.refinement.entries.Pairwise
      (fun first second => first.leftOwner.index ≤ second.leftOwner.index) := by
    rw [refinement_eq]
    exact Unit.Common.CommonRefinement.ofPartition_left_indices left.partition right.partition
      (Unit.Normalized.common left.partition right.partition)
      (fun _ member => Unit.Normalized.mem_common_left left.partition right.partition member)
      (fun _ member => Unit.Normalized.mem_common_right left.partition right.partition member)
  have retained : (common.readings.map CommonReading.entry).Pairwise
      (fun first second => first.leftOwner.index ≤ second.leftOwner.index) := by
    rw [common.entries_eq]
    exact ordered
  exact (Purelib.Data.List.Pairwise.pairwise_map (function := CommonReading.entry)
    (relation := fun first second => first.leftOwner.index ≤ second.leftOwner.index)).mp retained

/-- Common numerical readings retain nondecreasing original left-parent indices. -/
theorem commonReadings_left_indices {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    (commonReadings left right request).readings.Pairwise
      (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index) :=
  left_indices_of_common (commonReadings left right request) rfl

/-- Cache-selected common readings retain nondecreasing original left-parent indices. -/
theorem commonReadingsCached_left_indices {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    (commonReadingsCached left right cached request).readings.Pairwise
      (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index) :=
  left_indices_of_common (commonReadingsCached left right cached request) rfl

end Purelib.Integration.NumericalFrontier

end
