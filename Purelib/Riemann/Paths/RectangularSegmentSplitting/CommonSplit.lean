module

public import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts

/-! # Common ordered segment subdivisions for two retained rectangular grids

One union crossing partition is traversed once. Each child keeps the whole
original midpoint-selected piece in each grid, or that grid's exact finite
coverage request. Both grids, endpoints, ordered intervals and successful
partial work remain retained; no root or primitive observation is acquired.
-/

public section

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting

open Purelib
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts (point)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)

namespace GridCuts

variable {columns rows : Nat} {geometry : Geometry columns rows}
variable (cuts : GridCuts geometry) {first last : Canonical} {parameters : List Rational}
variable (partition : AxisPartition 0 1 parameters)
variable (included : ∀ parameter ∈ cuts.parameters first last, parameter ∈ parameters)
variable (interval : Interval) (member : interval ∈ partition.intervals)

/-- The exact finite assignment attempt retains either its original piece factory or failed midpoint coverage. -/
abbrev Assignment :=
  (Σ covered : {_value : Unit //
      Geometry.Covers geometry (point first last ((interval.lower + interval.upper) / 2))},
    {value : SegmentPiece geometry first last //
      value = cuts.assignIncluded (first := first) (last := last) partition
        included interval member covered.property}) ⊕
  {_value : Unit // ¬Geometry.Covers geometry (point first last ((interval.lower + interval.upper) / 2))}

/-- Check one actual child midpoint and retain the original full cell assignment on success.

The original axis-crossing proof supplies both closed endpoint incidences.
Failure is a finite coverage request for this exact child and grid, without
invalidating either grid or discarding another grid's successful work.
-/
def assignAttempt : cuts.Assignment (first := first) (last := last) partition included interval member := by
  letI : Decidable (Geometry.Covers geometry (point first last ((interval.lower + interval.upper) / 2))) := by
    unfold Geometry.Covers
    infer_instance
  if covered : Geometry.Covers geometry (point first last ((interval.lower + interval.upper) / 2)) then
    let piece := cuts.assignIncluded (first := first) (last := last) partition included interval member covered
    exact Sum.inl ⟨⟨(), covered⟩, ⟨piece, rfl⟩⟩
  else exact Sum.inr ⟨(), covered⟩

end GridCuts

variable {leftColumns leftRows rightColumns rightRows : Nat}
variable {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
variable (leftCuts : GridCuts leftGeometry) (rightCuts : GridCuts rightGeometry)
variable (first last : Canonical)

/-- The exact union crossing list keeps both original grid lists in their original order. -/
abbrev commonParameters : List Rational := leftCuts.parameters first last ++ rightCuts.parameters first last

/-- Each common child retains its ordinal interval and both complete original assignment outcomes. -/
abbrev CommonChild (partition : AxisPartition 0 1 (commonParameters leftCuts rightCuts first last)) :=
  Σ interval : {value : Interval // value ∈ partition.intervals},
    leftCuts.Assignment (first := first) (last := last) partition (fun _ member => List.mem_append_left _ member)
      interval.val interval.property ×
    rightCuts.Assignment (first := first) (last := last) partition (fun _ member => List.mem_append_right _ member)
      interval.val interval.property

namespace CommonChild

variable {leftCuts rightCuts first last}
variable {partition : AxisPartition 0 1 (commonParameters leftCuts rightCuts first last)}

/-- Construct both original-grid attempts at the SAME supplied ordinal child, without another partition. -/
def build (interval : Interval) (member : interval ∈ partition.intervals) :
    CommonChild leftCuts rightCuts first last partition :=
  let left := leftCuts.assignAttempt (first := first) (last := last) partition
    (fun _ present => List.mem_append_left _ present) interval member
  let right := rightCuts.assignAttempt (first := first) (last := last) partition
    (fun _ present => List.mem_append_right _ present) interval member
  ⟨⟨interval, member⟩, left, right⟩

/-- A child requires more coverage exactly when either retained assignment has its original negative outcome. -/
def needsCoverage (child : CommonChild leftCuts rightCuts first last partition) : Bool :=
  match child.2.1, child.2.2 with
  | Sum.inl _, Sum.inl _ => false
  | _, _ => true

/-- Retain every unresolved child in its original order, including either successful companion assignment. -/
def requests : List (CommonChild leftCuts rightCuts first last partition) →
    List (CommonChild leftCuts rightCuts first last partition)
  | [] => []
  | child :: remaining =>
      if child.needsCoverage then child :: requests remaining else requests remaining

/-- A retained left success belongs to this exact common ordinal interval. -/
theorem left_interval (child : CommonChild leftCuts rightCuts first last partition)
    (covered : {_value : Unit // Geometry.Covers leftGeometry
      (point first last ((child.1.val.lower + child.1.val.upper) / 2))})
    (piece : {value : SegmentPiece leftGeometry first last //
      value = leftCuts.assignIncluded (first := first) (last := last) partition
        (fun _ member => List.mem_append_left _ member)
        child.1.val child.1.property covered.property}) : piece.val.interval = child.1.val :=
  (congrArg SegmentPiece.interval piece.property).trans
    (leftCuts.assignIncluded_interval (first := first) (last := last) partition
      (fun _ member => List.mem_append_left _ member)
      child.1.val child.1.property covered.property)

/-- A retained right success belongs to this exact common ordinal interval. -/
theorem right_interval (child : CommonChild leftCuts rightCuts first last partition)
    (covered : {_value : Unit // Geometry.Covers rightGeometry
      (point first last ((child.1.val.lower + child.1.val.upper) / 2))})
    (piece : {value : SegmentPiece rightGeometry first last //
      value = rightCuts.assignIncluded (first := first) (last := last) partition
        (fun _ member => List.mem_append_right _ member)
        child.1.val child.1.property covered.property}) : piece.val.interval = child.1.val :=
  (congrArg SegmentPiece.interval piece.property).trans
    (rightCuts.assignIncluded_interval (first := first) (last := last) partition
      (fun _ member => List.mem_append_right _ member)
      child.1.val child.1.property covered.property)

/-- Both actual midpoint coverages make the original child attempts successful.

This proves only finite geometric coverage. It does not identify any
root, Point, Entry, primitive constant or signed occurrence.
-/
private theorem build_needsCoverage (interval : Interval) (member : interval ∈ partition.intervals)
    (leftInside : Geometry.Covers leftGeometry (point first last ((interval.lower + interval.upper) / 2)))
    (rightInside : Geometry.Covers rightGeometry (point first last ((interval.lower + interval.upper) / 2))) :
    (build (leftCuts := leftCuts) (rightCuts := rightCuts) (first := first) (last := last)
      interval member).needsCoverage = false := by
  unfold build GridCuts.assignAttempt needsCoverage
  rw [dif_pos leftInside, dif_pos rightInside]

end CommonChild

namespace CommonSplit

variable {leftCuts rightCuts first last}
variable (partition : AxisPartition 0 1 (commonParameters leftCuts rightCuts first last))

/-- Traverse the supplied interval list once, retaining each original membership and both grid outcomes. -/
def collect : (intervals : List Interval) → (∀ interval ∈ intervals, interval ∈ partition.intervals) →
    List (CommonChild leftCuts rightCuts first last partition)
  | [], _ => []
  | interval :: remaining, included =>
      CommonChild.build (leftCuts := leftCuts) (rightCuts := rightCuts)
        (first := first) (last := last) (partition := partition) interval (included _ List.mem_cons_self) ::
        collect remaining (fun _ member => included _ (List.mem_cons_of_mem _ member))

/-- Reading common-child intervals preserves the complete supplied ordered list. -/
private theorem collect_intervals (intervals : List Interval)
    (included : ∀ interval ∈ intervals, interval ∈ partition.intervals) :
    (collect (leftCuts := leftCuts) (rightCuts := rightCuts) (first := first) (last := last)
      partition intervals included).map (fun child => child.1.val) = intervals := by
  induction intervals with
  | nil => rfl
  | cons interval remaining ih =>
      change interval :: _ = interval :: remaining
      exact congrArg (List.cons interval) (ih _)

/-- Source endpoint coverage in both original grids resolves every actual common-child coverage request. -/
private theorem collect_requests_nil
    (leftFirst : Geometry.Covers leftGeometry first) (leftLast : Geometry.Covers leftGeometry last)
    (rightFirst : Geometry.Covers rightGeometry first) (rightLast : Geometry.Covers rightGeometry last)
    (intervals : List Interval) (included : ∀ interval ∈ intervals, interval ∈ partition.intervals) :
    CommonChild.requests (collect (leftCuts := leftCuts) (rightCuts := rightCuts)
      (first := first) (last := last) partition intervals included) = [] := by
  induction intervals with
  | nil => rfl
  | cons interval remaining ih =>
      have within := partition.interval_bounds (included interval List.mem_cons_self)
      have middle := PreparedSegmentCuts.midpoint_bounds interval
      have unit : 0 ≤ (interval.lower + interval.upper) / 2 ∧
          (interval.lower + interval.upper) / 2 ≤ 1 :=
        ⟨within.1.trans middle.1.le, middle.2.le.trans within.2⟩
      have done := CommonChild.build_needsCoverage (leftCuts := leftCuts) (rightCuts := rightCuts)
        (first := first) (last := last) (partition := partition) interval (included interval List.mem_cons_self)
        (Geometry.covers_point leftGeometry leftFirst leftLast unit)
        (Geometry.covers_point rightGeometry rightFirst rightLast unit)
      change (if (CommonChild.build (leftCuts := leftCuts) (rightCuts := rightCuts)
        (first := first) (last := last) (partition := partition)
          interval (included interval List.mem_cons_self)).needsCoverage then
        _ else _) = []
      rw [done]
      exact ih _

end CommonSplit

/-- Retain both old grids, the whole common partition, child/request factories and actual count. -/
abbrev CommonSplit :=
  {value : GridCuts leftGeometry × GridCuts rightGeometry × (Canonical × Canonical) //
    value = (leftCuts, rightCuts, (first, last))} ×
  (Σ partition : {value : AxisPartition 0 1 (commonParameters leftCuts rightCuts first last) //
      value = AxisPartition.build 0 1 (of_decide_eq_true rfl) (commonParameters leftCuts rightCuts first last)},
  Σ children : {value : List (CommonChild leftCuts rightCuts first last partition.val) //
      value = CommonSplit.collect (leftCuts := leftCuts) (rightCuts := rightCuts)
        (first := first) (last := last) partition.val partition.val.intervals (fun _ member => member)},
  {value : List (CommonChild leftCuts rightCuts first last partition.val) //
      value = CommonChild.requests children.val} ×
  {value : Nat // value = children.val.length})

namespace CommonSplit

/-- Materialize one union crossing partition and all original-grid child outcomes, then retain every unresolved request.

The geometry is finite metadata work. No Query, Point, Entry, root row,
primitive bank or OwnerJoin is acquired, reconstructed or identified here.
-/
def build : CommonSplit leftCuts rightCuts first last :=
  let partition := AxisPartition.build 0 1 (of_decide_eq_true rfl) (commonParameters leftCuts rightCuts first last)
  let children := collect (leftCuts := leftCuts) (rightCuts := rightCuts)
    (first := first) (last := last) partition partition.intervals (fun _ member => member)
  let requests := CommonChild.requests children
  let count := children.length
  (⟨(leftCuts, rightCuts, (first, last)), rfl⟩,
    ⟨⟨partition, rfl⟩, ⟨children, rfl⟩, ⟨requests, rfl⟩, ⟨count, rfl⟩⟩)

variable {leftCuts rightCuts first last} (split : CommonSplit leftCuts rightCuts first last)

/-- Read the SAME retained union crossing partition. -/
abbrev partition : AxisPartition 0 1 (commonParameters leftCuts rightCuts first last) := split.2.1.val

/-- Read every literal ordered child with its two original-grid outcomes. -/
abbrev children : List (CommonChild leftCuts rightCuts first last split.partition) := split.2.2.1.val

/-- Read the retained unresolved children, preserving all successful partial companion work. -/
abbrev requests : List (CommonChild leftCuts rightCuts first last split.partition) := split.2.2.2.1.val

/-- Read the actual common-child count without reusing an old one-grid ceiling. -/
abbrev count : Nat := split.2.2.2.2.val

/-- The complete original grid caches and ordered source endpoints remain unchanged. -/
theorem originals_eq : split.1.val = (leftCuts, rightCuts, (first, last)) := split.1.property

/-- The retained partition is the whole original factory on the actual union crossing list. -/
theorem partition_eq : split.partition = AxisPartition.build 0 1 (of_decide_eq_true rfl)
    (commonParameters leftCuts rightCuts first last) := split.2.1.property

/-- The whole child list retains its original collection factory on the SAME partition cache. -/
theorem children_eq : split.children = collect (leftCuts := leftCuts) (rightCuts := rightCuts)
    (first := first) (last := last) split.partition split.partition.intervals (fun _ member => member) :=
  split.2.2.1.property

/-- The retained requests are exactly the unresolved outcomes in that SAME whole child list. -/
theorem requests_eq : split.requests = CommonChild.requests split.children := split.2.2.2.1.property

/-- The retained count is the actual ordered child-list length. -/
theorem count_eq : split.count = split.children.length := split.2.2.2.2.property

/-- Both original grids share the SAME ordered parameter intervals without identifying root occurrences. -/
theorem intervals_eq : split.children.map (fun child => child.1.val) = split.partition.intervals := by
  rw [split.children_eq]
  exact collect_intervals split.partition _ _

/-- The common-child count is bounded by the actual two crossing-list lengths plus one. -/
theorem count_le : split.count ≤
    (leftCuts.parameters first last).length + (rightCuts.parameters first last).length + 1 := by
  have equal := congrArg List.length split.intervals_eq
  rw [Map.length_map, ← split.count_eq, ← split.partition.count_eq] at equal
  have bound := split.partition.count_le
  change split.partition.count ≤
    (leftCuts.parameters first last ++ rightCuts.parameters first last).length + 1 at bound
  rw [Append.length_append] at bound
  exact equal.trans_le bound

/-- An actually contained source segment needs no additional geometric coverage preparation in either original grid. -/
theorem requests_nil
    (leftFirst : Geometry.Covers leftGeometry first) (leftLast : Geometry.Covers leftGeometry last)
    (rightFirst : Geometry.Covers rightGeometry first) (rightLast : Geometry.Covers rightGeometry last) :
    split.requests = [] := by
  rw [split.requests_eq, split.children_eq]
  exact collect_requests_nil split.partition leftFirst leftLast rightFirst rightLast _ _

end CommonSplit

end Purelib.Riemann.Paths.RectangularSegmentSplitting

end
