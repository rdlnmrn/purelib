module
import Purelib.Data.List.Map

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.WindowAxes
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.List

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.WindowAxes

@[expose] public section

/-! Restricting the same cut bank to retained endpoints preserves exactly the
ordered interval list. This is the axis readback needed to compare whole-face
perimeters with the concatenated observation-piece perimeters. -/
namespace Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitionRestriction
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Coordinate Interval)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)

variable {lower upper first last : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} {cuts : List
  Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate}

/-- An increasing walk with no retained coordinate inside its endpoints is one actual retained interval. -/
private theorem retained_edge (outer : AxisPartition lower upper cuts)
    {start finish : PreparedAxisPartitions.Coordinate} (walk : AxisWalks.IncreasingWalk outer.intervals start finish)
    (proper : start < finish)
    (outside : ∀ point ∈ outer.coordinates, point ≤ start ∨ finish ≤ point) :
    ∃ interval ∈ outer.intervals, interval.lower = start ∧ interval.upper = finish := by
  cases walk with
  | nil => exact (lt_irrefl _ proper).elim
  | cons interval member tail =>
      have endpoint := (Interval.endpoints_mem outer.coordinates outer.ordered
        (outer.intervals_eq ▸ member)).2
      rcases outside interval.upper endpoint with before | after
      · exact (not_lt_of_ge before interval.ordered).elim
      · exact ⟨interval, member, rfl, le_antisymm tail.ordered after⟩

/-- A piece using the same cuts contains actual intervals of the whole bank. The piece endpoints must already be
retained; otherwise this claim is false. -/
theorem interval_mem_of_restriction (outer : AxisPartition lower upper cuts) (inner :
  AxisPartition first last cuts)
    (firstInside : lower ≤ first) (lastInside : last ≤ upper)
    (firstRetained : first ∈ outer.coordinates) (lastRetained : last ∈ outer.coordinates)
    {interval : PreparedAxisPartitions.Interval} (member : interval ∈ inner.intervals) : interval ∈ outer.intervals :=
      by
  have included (point : PreparedAxisPartitions.Coordinate) (present : point ∈ inner.coordinates) : point ∈
    outer.coordinates := by
    rcases (inner.coordinates_spec point).mp present with rfl | rfl | present
    · exact firstRetained
    · exact lastRetained
    · exact outer.cut_mem present.1 ⟨firstInside.trans present.2.1, present.2.2.trans lastInside⟩
  have endpoints := Interval.endpoints_mem inner.coordinates inner.ordered
    (inner.intervals_eq ▸ member)
  have firstMember : interval.lower ∈ outer.coordinates.map id :=
    Map.mem_map_of_mem (included _ endpoints.1)
  have lastMember : interval.upper ∈ outer.coordinates.map id :=
    Map.mem_map_of_mem (included _ endpoints.2)
  let walk := AxisWalks.increasing interval.lower interval.upper outer.coordinates outer.ordered
    firstMember lastMember interval.ordered.le
  have outerWalk : AxisWalks.IncreasingWalk outer.intervals interval.lower interval.upper := outer.intervals_eq.symm ▸
    walk
  have outside (point : PreparedAxisPartitions.Coordinate) (present : point ∈ outer.coordinates) :
      point ≤ interval.lower ∨ interval.upper ≤ point := by
    rcases (outer.coordinates_spec point).mp present with rfl | rfl | present
    · exact Or.inl (firstInside.trans (inner.interval_bounds member).1)
    · exact Or.inr ((inner.interval_bounds member).2.trans lastInside)
    · exact inner.cut_outside member present.1
  obtain ⟨retained, retainedMember, lowerEq, upperEq⟩ :=
    retained_edge outer outerWalk interval.ordered outside
  have equal : retained = interval := by
    cases retained
    cases interval
    cases lowerEq
    cases upperEq
    rfl
  exact equal ▸ retainedMember

/-- Transport an increasing walk into a larger interval bank while preserving its edges. -/
private def includeWalk {small large : List Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  (included : ∀ interval ∈ small, interval ∈ large) :
    {start finish : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk small start finish →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk large start finish
  | _, _, .nil point => .nil point
  | _, _, .cons interval member tail => .cons interval (included interval member)
    (includeWalk included tail)

/-- Transporting interval membership leaves the walk's edge list unchanged. -/
private theorem includeWalk_edges {small large : List PreparedAxisPartitions.Interval} (included : ∀ interval ∈ small,
  interval ∈ large) :
    {start finish : PreparedAxisPartitions.Coordinate} → (walk : AxisWalks.IncreasingWalk small start finish) →
      (includeWalk included walk).edges = walk.edges
  | _, _, .nil _ => rfl
  | _, _, .cons interval _ tail => congrArg (List.cons interval)
    (includeWalk_edges included tail)

/-- Exact list equality retains the original order and multiplicity, not just coverage or the sum of interval widths. -/
theorem intervals_restriction (outer : AxisPartition lower upper cuts) (inner :
  AxisPartition first last cuts)
    (firstInside : lower ≤ first) (lastInside : last ≤ upper)
    (firstRetained : first ∈ outer.coordinates) (lastRetained : last ∈ outer.coordinates) :
    inner.intervals = outer.intervals.filter
      (fun interval => decide (first ≤ interval.lower ∧ interval.upper ≤ last)) := by
  let included := fun interval member =>
    interval_mem_of_restriction outer inner firstInside
    lastInside
    firstRetained lastRetained (interval := interval) member
  let walk := includeWalk included inner.walk
  exact inner.walk_edges.symm.trans ((includeWalk_edges
    included inner.walk).symm.trans
    (IncreasingWalk.edges_eq_filter outer.separated walk))

/-- Concatenate increasing walks whose joining endpoints agree. -/
private def appendWalk {intervals : List Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval} :
    {start middle finish : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals start middle →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals middle finish →
        Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals start finish
  | _, _, _, .nil _, last => last
  | _, _, _, .cons interval member tail, last => .cons interval member
    (appendWalk tail last)

/-- The concatenated walk traverses the concatenated edge lists. -/
private theorem appendWalk_edges {intervals : List PreparedAxisPartitions.Interval} :
    {start middle finish : PreparedAxisPartitions.Coordinate} → (first : AxisWalks.IncreasingWalk intervals start
      middle) →
      (last : AxisWalks.IncreasingWalk intervals middle finish) →
      (appendWalk first last).edges = first.edges ++
        last.edges
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons interval _ tail, last => congrArg (List.cons interval)
    (appendWalk_edges tail last)

/-- Splitting at a retained cut preserves the complete interval spine. This is the concatenation identity needed for
subdivided perimeter traces. -/
theorem intervals_split {middle : PreparedAxisPartitions.Coordinate} (outer : AxisPartition lower
  upper cuts)
    (left : AxisPartition lower middle cuts) (right : AxisPartition middle upper
      cuts)
    (retained : middle ∈ outer.coordinates) :
    outer.intervals = left.intervals ++ right.intervals := by
  let leftIncluded := fun interval member =>
    interval_mem_of_restriction outer left le_rfl
    right.proper.le
    outer.lower_mem retained (interval := interval) member
  let rightIncluded := fun interval member =>
    interval_mem_of_restriction outer right left.proper.le
    le_rfl
    retained outer.upper_mem (interval := interval) member
  let first := includeWalk leftIncluded left.walk
  let last := includeWalk rightIncluded right.walk
  have same := (IncreasingWalk.edges_eq_filter outer.separated outer.walk).trans
    (IncreasingWalk.edges_eq_filter outer.separated
      (appendWalk first last)).symm
  exact outer.walk_edges.symm.trans (same.trans
    ((appendWalk_edges first last).trans
    (congrArg₂ List.append ((includeWalk_edges
      leftIncluded left.walk).trans left.walk_edges)
      ((includeWalk_edges rightIncluded right.walk).trans
        right.walk_edges))))

/-- Construct the increasing retained walk between two ordered cached coordinates. -/
private def between (outer : AxisPartition lower upper cuts) (start finish :
  PreparedAxisPartitions.Coordinate)
    (firstMember : start ∈ outer.coordinates) (lastMember : finish ∈ outer.coordinates)
    (forward : start ≤ finish) : AxisWalks.IncreasingWalk outer.intervals start finish :=
  outer.intervals_eq.symm ▸ AxisWalks.increasing start finish outer.coordinates outer.ordered
    (Map.mem_map_of_mem firstMember) (Map.mem_map_of_mem lastMember) forward

/-- Replace each coarse walk edge by the retained fine walk between its endpoints.

Every coarse endpoint must belong to the original fine coordinate bank. -/
private def refineWalk (outer : AxisPartition lower upper cuts)
  {coarse : List Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
    (retained : ∀ interval ∈ coarse, interval.lower ∈ outer.coordinates ∧ interval.upper ∈ outer.coordinates) :
    {start finish : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk coarse start finish →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk outer.intervals start finish
  | _, _, .nil point => .nil point
  | _, _, .cons interval member tail => appendWalk
      (between outer interval.lower interval.upper
        (retained interval member).1 (retained interval member).2 interval.ordered.le)
      (refineWalk outer retained tail)

/-- The refined walk lists the fine intervals contained in each coarse edge, in traversal order. -/
private theorem refineWalk_edges (outer : AxisPartition lower upper cuts) {coarse : List
  PreparedAxisPartitions.Interval}
    (retained : ∀ interval ∈ coarse, interval.lower ∈ outer.coordinates ∧ interval.upper ∈ outer.coordinates) :
    {start finish : PreparedAxisPartitions.Coordinate} → (walk : AxisWalks.IncreasingWalk coarse start finish) →
      (refineWalk outer retained walk).edges =
        walk.edges.flatMap (fun interval =>
        outer.intervals.filter (fun fine => decide (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper)))
  | _, _, .nil _ => rfl
  | _, _, .cons interval member tail => by
      change (appendWalk _ _).edges = _
      exact (appendWalk_edges _ _).trans (congrArg₂
        List.append
        (IncreasingWalk.edges_eq_filter outer.separated
          (between outer interval.lower interval.upper
            (retained interval member).1
          (retained interval member).2 interval.ordered.le))
        (refineWalk_edges outer retained tail))

/-- Any finite coarse partition refines to the full ordered fine bank when all its endpoints are retained. No piece is
omitted or counted twice. -/
theorem intervals_flatMap {coarseCuts : List PreparedAxisPartitions.Coordinate} (outer :
  AxisPartition lower upper cuts)
    (coarse : AxisPartition lower upper coarseCuts)
    (retained : ∀ interval ∈ coarse.intervals,
      interval.lower ∈ outer.coordinates ∧ interval.upper ∈ outer.coordinates) :
    outer.intervals = coarse.intervals.flatMap (fun interval =>
      outer.intervals.filter (fun fine => decide (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper))) := by
  have same := (IncreasingWalk.edges_eq_filter outer.separated outer.walk).trans
    (IncreasingWalk.edges_eq_filter outer.separated
      (refineWalk outer retained coarse.walk)).symm
  exact outer.walk_edges.symm.trans (same.trans
    ((refineWalk_edges outer retained coarse.walk).trans
    (congrArg (fun intervals => intervals.flatMap (fun interval =>
      outer.intervals.filter (fun fine => decide (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper))))
      coarse.walk_edges)))

end Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitionRestriction
