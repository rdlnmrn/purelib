module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Cell.Partitioned
public import Purelib.Integration.Partition.Unit.Common
import Purelib.Data.List.GetD
import Purelib.Data.List.Map
import Purelib.Data.List.Attach
import Purelib.Data.List.Membership
import Purelib.Data.List.Pairwise
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! Common tagged readings with the two original indexed parent owners. -/

public section

namespace Purelib.Integration

open Purelib.Data.Rat
open Purelib.Integration.Partition

namespace SourceFrontier

/-- View the original source frontier as its exact partitioned cell occurrences. -/
theorem partitioned {source : Fraction.Rational → Fraction.Rational} (frontier : SourceFrontier source) :
    PartitionedCells frontier.partition frontier.cells (fun point => point.interval) :=
  ⟨frontier.domains_eq, frontier.weight_eq⟩

set_option genInjectivity false in
/-- Source readings at one common child, retaining both original parent cells.

The entry owns the child in both original partitions. Each cached parent cell
is selected at that owner's original index. The two readings use the same
retained rational tag and are contained in their own parent ranges. -/
structure CommonReading {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) where
  /-- The original common child and both indexed parent owners. -/ entry :
    Unit.Common.CommonEntry left.partition right.partition
  /-- The exact common child is a positive-length interval inside the unit interval. -/ valid : entry.child.Valid
  /-- The retained rational point at which both original sources are read. -/ tag : Fraction.Rational
  /-- The common tag is contained in the original closed child interval. -/ tag_inside :
    entry.child.start ≤ tag ∧ tag ≤ entry.child.finish
  /-- The actual left cell at the retained left parent index. -/ leftCell :
    {cell : IntegrationCell (SourcePoint leftSource) //
      Purelib.Data.List.getElem? left.cells entry.leftOwner.index = some cell ∧
        cell.item.interval = entry.leftOwner.parent}
  /-- The actual right cell at the retained right parent index. -/ rightCell :
    {cell : IntegrationCell (SourcePoint rightSource) //
      Purelib.Data.List.getElem? right.cells entry.rightOwner.index = some cell ∧
        cell.item.interval = entry.rightOwner.parent}
  /-- The left source's cached or freshly requested reading at the common tag. -/ leftReading : Fraction.Rational
  /-- The right source's cached or freshly requested reading at the common tag. -/ rightReading : Fraction.Rational
  /-- The left reading is produced by the original parent cell's read operation. -/ left_reading_eq :
    leftReading = leftCell.val.item.readAt tag
  /-- The right reading is produced by the original parent cell's read operation. -/ right_reading_eq :
    rightReading = rightCell.val.item.readAt tag
  /-- The left parent's range encloses its original common-point reading. -/ left_inside :
    leftCell.val.lower ≤ leftReading ∧ leftReading ≤ leftCell.val.upper
  /-- The right parent's range encloses its original common-point reading. -/ right_inside :
    rightCell.val.lower ≤ rightReading ∧ rightReading ≤ rightCell.val.upper

constructive_injectivity CommonReading

/-- View the actual left common reading as a reusable point of its original source.

The common child and tag remain attached to the same cached scalar; forming
the view does not evaluate the source again. -/
@[expose] def CommonReading.leftPoint {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (reading : CommonReading left right) : SourcePoint leftSource :=
  ⟨reading.entry.child, reading.tag, reading.tag_inside.1, reading.tag_inside.2,
    reading.leftReading, reading.left_reading_eq.trans (reading.leftCell.val.item.readAt_eq reading.tag)⟩

/-- View the actual right common reading as a reusable point of its original source.

The common child and tag remain attached to the same cached scalar; forming
the view does not evaluate the source again. -/
@[expose] def CommonReading.rightPoint {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (reading : CommonReading left right) : SourcePoint rightSource :=
  ⟨reading.entry.child, reading.tag, reading.tag_inside.1, reading.tag_inside.2,
    reading.rightReading, reading.right_reading_eq.trans (reading.rightCell.val.item.readAt_eq reading.tag)⟩

/-- Two exact source readings at the same tag, tied to the original parent point observations. -/
abbrev ReadingPair {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourcePoint leftSource) (right : SourcePoint rightSource) (tag : Fraction.Rational) :=
  {values : Fraction.Rational × Fraction.Rational //
    values.1 = left.readAt tag ∧ values.2 = right.readAt tag}

/-- Read both original parent points independently at their shared rational tag. -/
@[expose] def independentPair {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourcePoint leftSource) (right : SourcePoint rightSource) (tag : Fraction.Rational) :
    ReadingPair left right tag :=
  ⟨⟨left.readAt tag, right.readAt tag⟩, rfl, rfl⟩

/-- Use one retained or fresh reading for both parents of the same exact source. -/
@[expose] def cachedPair {source : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint source))
    (left right : SourcePoint source) (tag : Fraction.Rational) : ReadingPair left right tag :=
  let reading := SourcePoint.readCached source cached tag
  ⟨⟨reading, reading⟩, (SourcePoint.readCached_eq source cached tag).trans (left.readAt_eq tag).symm,
    (SourcePoint.readCached_eq source cached tag).trans (right.readAt_eq tag).symm⟩

/-- All certified pairs retain the same original exact readings. -/
theorem readingPair_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourcePoint leftSource} {right : SourcePoint rightSource} {tag : Fraction.Rational}
    (pair : ReadingPair left right tag) : pair = independentPair left right tag := by
  apply Subtype.ext
  exact Prod.ext pair.property.1 pair.property.2

/-- Assemble a common child from the supplied readings of its original parent cells.

The constructor selects both original parent occurrences, reads the retained
child tag and derives the two range certificates from their source laws. -/
@[expose] def readCommonFromPair {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish)
    (pair : ReadingPair (left.partitioned.cellAtOwner entry.leftOwner).val.item
      (right.partitioned.cellAtOwner entry.rightOwner).val.item tag) : CommonReading left right := by
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
  have leftInside := left.source_range leftCell.val leftMember tag leftStart leftFinish
  have rightInside := right.source_range rightCell.val rightMember tag rightStart rightFinish
  have leftRead := leftCell.val.item.readAt_eq tag
  have rightRead := rightCell.val.item.readAt_eq tag
  exact
    { entry := entry
      valid := valid
      tag := tag
      tag_inside := tagInside
      leftCell := leftCell
      rightCell := rightCell
      leftReading := pair.val.1
      rightReading := pair.val.2
      left_reading_eq := pair.property.1
      right_reading_eq := pair.property.2
      left_inside := by rw [pair.property.1, leftRead]; exact leftInside
      right_inside := by rw [pair.property.2, rightRead]; exact rightInside }

/-- Read a rational tag in a valid common child from both original source frontiers.

The supplied reader consumes the original indexed parent cells and shared tag;
its returned pair supplies the retained readings and their range certificates. -/
@[expose] def readCommonWith {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (reader : (left : SourcePoint leftSource) → (right : SourcePoint rightSource) →
      (tag : Fraction.Rational) → ReadingPair left right tag)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish) :
    CommonReading left right :=
  readCommonFromPair left right entry valid tag tagInside
    (reader (left.partitioned.cellAtOwner entry.leftOwner).val.item
      (right.partitioned.cellAtOwner entry.rightOwner).val.item tag)

/-- Read a common child independently from both original source owners. -/
@[expose] def readCommon {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish) :
    CommonReading left right :=
  readCommonWith left right independentPair entry valid tag tagInside

/-- A certified reading pair preserves the complete original common-child reading. -/
theorem readCommonWith_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (reader : (left : SourcePoint leftSource) → (right : SourcePoint rightSource) →
      (tag : Fraction.Rational) → ReadingPair left right tag)
    (entry : Unit.Common.CommonEntry left.partition right.partition) (valid : entry.child.Valid)
    (tag : Fraction.Rational) (tagInside : entry.child.start ≤ tag ∧ tag ≤ entry.child.finish) :
    readCommonWith left right reader entry valid tag tagInside = readCommon left right entry valid tag tagInside := by
  unfold readCommon readCommonWith
  simp only [-eq_self, -iff_self, readingPair_eq]
  rfl

set_option genInjectivity false in
/-- An ordered common refinement with both original readings at every retained child.

The exact entries of the cached common partition are recovered from the
readings in order, retaining each child's two indexed parent owners. -/
structure CommonReadings {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) where
  /-- The computed common refinement of the two original partitions. -/ refinement :
    Unit.Common.CommonRefinement left.partition right.partition
  /-- The ordered common-point readings for the exact retained children. -/ readings : List (CommonReading left right)
  /-- Reading child entries gives the original common refinement's exact ordered entries. -/ entries_eq :
    readings.map CommonReading.entry = refinement.entries

constructive_injectivity CommonReadings

/-- Common-reading collections with the same refinement and ordered readings are equal. -/
theorem CommonReadings.ext {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (first second : CommonReadings left right) (refinement_eq : first.refinement = second.refinement)
    (readings_eq : first.readings = second.readings) : first = second := by
  cases first with
  | mk firstRefinement firstReadings firstEntries =>
    cases second with
    | mk secondRefinement secondReadings secondEntries =>
      cases refinement_eq
      cases readings_eq
      rfl

/-- Read each child of a retained common refinement at its supplied rational tag.

The tag rule is certified on every valid rational child. Each original parent
owner selects its exact retained cell, and both source readings remain
available even when the sources differ. -/
@[expose] def readRefinementWith {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (reader : (left : SourcePoint leftSource) → (right : SourcePoint rightSource) →
      (tag : Fraction.Rational) → ReadingPair left right tag)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (tag : Partition.Interval → Fraction.Rational)
    (tagInside : ∀ interval, interval.Valid → interval.start ≤ tag interval ∧ tag interval ≤ interval.finish) :
    CommonReadings left right := by
  let readings : List (CommonReading left right) := refinement.entries.attach.map fun
      (entry : {entry // entry ∈ refinement.entries}) =>
    let valid : entry.val.child.Valid := by
      have childMember : entry.val.child ∈ refinement.partition.intervals := by
        rw [← refinement.children_eq]
        exact (Purelib.Data.List.Map.mem_map).mpr ⟨entry.val, entry.property, rfl⟩
      exact refinement.partition.valid entry.val.child childMember
    readCommonWith left right reader entry.val valid (tag entry.val.child) (tagInside entry.val.child valid)
  exact
    { refinement := refinement
      readings := readings
      entries_eq := by
        change (refinement.entries.attach.map _).map CommonReading.entry = refinement.entries
        rw [Purelib.Data.List.Map.map_map]
        change refinement.entries.attach.map Subtype.val = refinement.entries
        exact Purelib.Data.List.attach_map_subtype_val _ }

/-- Read the common refinement independently from both original source owners. -/
@[expose] def readRefinement {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (tag : Partition.Interval → Fraction.Rational)
    (tagInside : ∀ interval, interval.Valid → interval.start ≤ tag interval ∧ tag interval ≤ interval.finish) :
    CommonReadings left right :=
  readRefinementWith left right independentPair refinement tag tagInside

/-- Any certified reading-pair constructor preserves the original ordered common refinement. -/
theorem readRefinementWith_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (reader : (left : SourcePoint leftSource) → (right : SourcePoint rightSource) →
      (tag : Fraction.Rational) → ReadingPair left right tag)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (tag : Partition.Interval → Fraction.Rational)
    (tagInside : ∀ interval, interval.Valid → interval.start ≤ tag interval ∧ tag interval ≤ interval.finish) :
    readRefinementWith left right reader refinement tag tagInside =
      readRefinement left right refinement tag tagInside := by
  refine CommonReadings.ext _ _ ?_ ?_
  · rfl
  · change refinement.entries.attach.map _ = refinement.entries.attach.map _
    apply Purelib.Data.List.Map.map_congr_left
    intro entry _
    apply readCommonWith_eq

/-- Compute common readings of one source using its actual bank of retained exact observations. -/
@[expose] def commonReadingsCached {source : Fraction.Rational → Fraction.Rational}
    (left right : SourceFrontier source) (cached : List (SourcePoint source)) : CommonReadings left right :=
  readRefinementWith left right (cachedPair cached) (Unit.Common.commonRefinement left.partition right.partition)
    Partition.Interval.start (fun _ valid => ⟨le_rfl, valid.2.1.le⟩)

/-- Compute the original common refinement and read its children with a supplied rational tag rule. -/
@[expose] def commonReadingsWithTags {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (tag : Partition.Interval → Fraction.Rational)
    (tagInside : ∀ interval, interval.Valid → interval.start ≤ tag interval ∧ tag interval ≤ interval.finish) :
    CommonReadings left right :=
  readRefinement left right (Unit.Common.commonRefinement left.partition right.partition) tag tagInside

/-- Compute common readings using the retained children's left endpoints as tags. -/
@[expose] def commonReadings {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) : CommonReadings left right :=
  commonReadingsWithTags left right Partition.Interval.start (fun _ valid => ⟨le_rfl, valid.2.1.le⟩)

/-- Cache-selected common readings preserve the complete original common refinement. -/
theorem commonReadingsCached_eq {source : Fraction.Rational → Fraction.Rational}
    (left right : SourceFrontier source) (cached : List (SourcePoint source)) :
    commonReadingsCached left right cached = commonReadings left right :=
  readRefinementWith_eq left right (cachedPair cached)
    (Unit.Common.commonRefinement left.partition right.partition) Partition.Interval.start
    (fun _ valid => ⟨le_rfl, valid.2.1.le⟩)

/-- The computed common readings retain nondecreasing indices into the original left frontier. -/
theorem commonReadings_left_indices {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    (commonReadings left right).readings.Pairwise
      (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index) := by
  let common := commonReadings left right
  have ordered : common.refinement.entries.Pairwise
      (fun first second => first.leftOwner.index ≤ second.leftOwner.index) := by
    change (Unit.Common.commonRefinement left.partition right.partition).entries.Pairwise _
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

namespace CommonReading

/-- Equal rational source restrictions give equal actual readings at this retained common point. -/
theorem readings_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource} (reading : CommonReading left right)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) :
    reading.leftReading = reading.rightReading := by
  rw [reading.left_reading_eq, reading.right_reading_eq,
    reading.leftCell.val.item.readAt_eq, reading.rightCell.val.item.readAt_eq]
  exact same reading.tag (reading.valid.1.trans reading.tag_inside.1) (reading.tag_inside.2.trans reading.valid.2.2)

/-- Turn the retained common point into an exact weighted cell of its original child length.

The payload is the complete common reading, including both original parent
owners and both actual source replies. Its exact range is the left reply. -/
@[expose] def exactCell {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (reading : CommonReading left right) : IntegrationCell (CommonReading left right) :=
  IntegrationCell.exact reading reading.entry.child.signedLength reading.leftReading
    (Partition.Interval.signedLength_pos reading.valid).le

end CommonReading

namespace CommonReadings

/-- The exact common tagged cells, preserving every retained child and both source owners. -/
@[expose] def cells {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) : List (IntegrationCell (CommonReading left right)) :=
  common.readings.map CommonReading.exactCell

/-- The common cells read back to the actual common partition's ordered intervals. -/
theorem cells_domains {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) :
    common.cells.map (fun cell => cell.item.entry.child) = common.refinement.partition.intervals := by
  unfold cells
  rw [Purelib.Data.List.Map.map_map]
  change common.readings.map (fun reading => reading.entry.child) = common.refinement.partition.intervals
  calc
    _ = (common.readings.map CommonReading.entry).map Unit.Common.CommonEntry.child :=
      (Purelib.Data.List.Map.map_map Unit.Common.CommonEntry.child CommonReading.entry common.readings).symm
    _ = common.refinement.partition.intervals := by
      rw [common.entries_eq, common.refinement.children_eq]

/-- The common tagged cells retain exact unit total weight. -/
theorem totalWeight {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) : integrationWeight common.cells = 1 := by
  have lengths : ∀ cell ∈ common.cells, cell.weight = cell.item.entry.child.signedLength := by
    intro cell member
    rcases (Purelib.Data.List.Map.mem_map).mp member with ⟨reading, _, equal⟩
    cases equal
    rfl
  rw [integrationWeight_eq_lengthSum (fun reading : CommonReading left right => reading.entry.child)
    common.cells lengths, common.cells_domains]
  exact common.refinement.partition.lengthSum

/-- The left source's actual common-point readings weighted by their original child lengths. -/
@[expose] def leftSum {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) : Fraction.Rational :=
  weightedEvaluation CommonReading.leftReading common.cells

/-- The right source's actual common-point readings weighted by the same original child lengths. -/
@[expose] def rightSum {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) : Fraction.Rational :=
  weightedEvaluation CommonReading.rightReading common.cells

/-- The length-weighted absolute discrepancy of the two actual common-point readings. -/
@[expose] def pointBudget {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) : Fraction.Rational :=
  weightedEvaluation (fun reading => Fraction.abs (reading.leftReading - reading.rightReading)) common.cells

/-- The actual common tagged sums differ by at most the retained weighted reading discrepancy. -/
theorem sum_difference_le_pointBudget {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) :
    Fraction.abs (common.leftSum - common.rightSum) ≤ common.pointBudget :=
  weightedEvaluation_abs_sub_le CommonReading.leftReading CommonReading.rightReading common.cells

/-- Equal retained readings give equal weighted sums on any displayed common cells. -/
private theorem weighted_readings_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource} :
    (∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) →
    ∀ cells : List (IntegrationCell (CommonReading left right)),
      weightedEvaluation CommonReading.leftReading cells = weightedEvaluation CommonReading.rightReading cells
  | _, [] => rfl
  | same, cell :: remaining => by
      change cell.weight * cell.item.leftReading + weightedEvaluation CommonReading.leftReading remaining =
        cell.weight * cell.item.rightReading + weightedEvaluation CommonReading.rightReading remaining
      rw [cell.item.readings_eq same, weighted_readings_eq same remaining]

/-- Equal source restrictions make every retained point-discrepancy contribution zero. -/
private theorem weighted_discrepancy_eq_zero {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (same : ∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) :
    ∀ cells : List (IntegrationCell (CommonReading left right)),
      weightedEvaluation (fun reading => Fraction.abs (reading.leftReading - reading.rightReading)) cells = 0
  | [] => rfl
  | cell :: remaining => by
      change cell.weight * Fraction.abs (cell.item.leftReading - cell.item.rightReading) +
        weightedEvaluation (fun reading => Fraction.abs (reading.leftReading - reading.rightReading)) remaining = 0
      rw [cell.item.readings_eq same]
      have difference : cell.item.rightReading - cell.item.rightReading = 0 := by ring1
      rw [difference]
      change cell.weight * 0 +
        weightedEvaluation (fun reading => Fraction.abs (reading.leftReading - reading.rightReading)) remaining = 0
      rw [Fraction.Field.mul_zero_direct, Fraction.Field.zero_add, weighted_discrepancy_eq_zero same remaining]

/-- Equal rational source restrictions make the actual weighted point budget exactly zero. -/
theorem pointBudget_eq_zero {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) : common.pointBudget = 0 :=
  weighted_discrepancy_eq_zero same common.cells

/-- Both original sources give the same weighted sum on the computed common tags. -/
theorem leftSum_eq_rightSum {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) :
    common.leftSum = common.rightSum :=
  weighted_readings_eq same common.cells

end CommonReadings

end SourceFrontier

end Purelib.Integration

end
