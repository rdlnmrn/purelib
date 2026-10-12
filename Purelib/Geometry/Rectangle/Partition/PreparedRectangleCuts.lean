module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.Nat.Multiplication
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Geometry.Rational.Box.Separation

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Rectangular partitions through a prescribed finite point bank

The Cartesian product of the two cached cut partitions has proper,
interior-disjoint cells, exact total area, and at most `(points.length + 1)^2`
rectangles. Every requested point inside the original box is an actual
corner of a returned rectangle, including outer-boundary and repeated points.
-/

namespace Purelib.Geometry.Rectangle

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Geometry
open Purelib.Geometry.Rational.Box
open Purelib.Geometry.Rational.Box.Gaussian
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Topology.Mesh
open Purelib.Data.List

open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Coordinate Interval)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (Box Gaussian sumCells sumCells_append)

namespace Partition.PreparedRectangleCuts

/-- Construct the box determined by two proper coordinate intervals.

The two retained proper intervals supply the box endpoints and their order
certificates. The construction keeps the original horizontal and vertical
interval identities. -/
@[expose] public def intervalBox (horizontal vertical : Interval) : Box :=
  ⟨horizontal.lower, horizontal.upper, vertical.lower, vertical.upper, horizontal.ordered.le, vertical.ordered.le⟩

/-- List the Cartesian product of horizontal and vertical intervals in row-major
order.

Each horizontal interval supplies one complete row of the retained vertical
list. The original outer and inner occurrence orders are preserved. -/
@[expose] public def rectangles (horizontal vertical : List Interval) : List Box :=
  horizontal.flatMap fun x => vertical.map (intervalBox x)

/-- A listed rectangle is exactly the box of an actual horizontal and vertical
interval pair.

The two witnesses retain membership in their original interval banks. The
resulting equality identifies the displayed rectangle without replacing either
interval. -/
private theorem rectangles_mem {horizontal vertical : List Interval} {box : PreparedBoxPartitions.Box} :
    box ∈ rectangles horizontal vertical ↔
      ∃ x ∈ horizontal, ∃ y ∈ vertical, intervalBox x y = box := by
  constructor
  · intro member
    obtain ⟨x, xMember, inRow⟩ := Flatten.mem_flatMap.mp member
    obtain ⟨y, yMember, equal⟩ := Map.mem_map.mp inRow
    exact ⟨x, xMember, y, yMember, equal⟩
  · rintro ⟨x, xMember, y, yMember, equal⟩
    exact Flatten.mem_flatMap.mpr ⟨x, xMember, Map.mem_map.mpr ⟨y, yMember, equal⟩⟩

/-- The Cartesian rectangle count is the product of the two interval counts.

Every horizontal occurrence contributes one mapped vertical row. Structural
concatenation therefore multiplies the two retained interval-list lengths. -/
private theorem rectangles_length (horizontal vertical : List Interval) :
    (rectangles horizontal vertical).length = horizontal.length * vertical.length := by
  induction horizontal with
  | nil => exact (Nat.zero_mul _).symm
  | cons first rest ih =>
      simp only [rectangles, Flatten.flatMap_cons, Append.length_append, Map.length_map,
        List.length_cons] at *
      rw [ih, Data.Nat.Multiplication.right_distrib, Nat.one_mul, Nat.add_comm]

/-- An ordered vertical interval list gives pairwise interior-separated boxes in
one column.

The horizontal interval is fixed across the row. Vertical pairwise endpoint
order provides interior separation for each displayed pair of boxes. -/
private theorem row_separated (horizontal : Interval) (vertical : List Interval)
    (ordered : vertical.Pairwise Interval.Before) :
    (vertical.map (intervalBox horizontal)).Pairwise
      Rational.Box.InteriorSeparated := by
  apply Pairwise.pairwise_map.mpr
  exact ordered.imp (fun before => Or.inr (Or.inr (Or.inl before)))

/-- Pairwise ordered axes give pairwise interior-separated Cartesian boxes.

Intervals within a row are separated vertically; boxes in different rows are
separated horizontally. Both certificates refer to the original ordered axis
banks. -/
private theorem rectangles_separated (horizontal vertical : List Interval)
    (xOrdered : horizontal.Pairwise Interval.Before)
    (yOrdered : vertical.Pairwise Interval.Before) :
    (rectangles horizontal vertical).Pairwise Rational.Box.InteriorSeparated := by
  induction horizontal with
  | nil => exact .nil
  | cons first rest ih =>
      change ((vertical.map (intervalBox first)) ++ rectangles rest
        vertical).Pairwise _
      apply Pairwise.pairwise_append (row_separated first vertical yOrdered) (ih
        (List.pairwise_cons.mp xOrdered).2)
      intro left leftMember right rightMember
      obtain ⟨y, _, rfl⟩ := Map.mem_map.mp leftMember
      obtain ⟨x, xMember, y', _, rfl⟩ := PreparedRectangleCuts.rectangles_mem.mp rightMember
      exact Or.inl ((List.pairwise_cons.mp xOrdered).1 x xMember)

/-- The area sum in one column is its width times the total vertical width.

The horizontal width is fixed across the retained vertical list. Scalar
distributivity factors it from the original finite area accumulation. -/
private theorem row_area (horizontal : Interval) (vertical : List Interval) :
    PreparedBoxPartitions.sumCells Content.boxContent (vertical.map (intervalBox horizontal)) =
      (horizontal.upper - horizontal.lower) * AxisPartition.widthSum vertical := by
  induction vertical with
  | nil => change (0 : Coordinate) = _ * 0; ring1
  | cons first rest ih =>
      change (horizontal.upper - horizontal.lower) * (first.upper - first.lower) +
        PreparedBoxPartitions.sumCells Content.boxContent (rest.map (intervalBox horizontal)) = _
      rw [ih]
      change _ = (horizontal.upper - horizontal.lower) *
        ((first.upper - first.lower) + AxisPartition.widthSum rest)
      ring1

/-- The Cartesian area sum is the product of the two axis width sums.

Each original horizontal row contributes its width times the retained vertical
width sum. Adding the rows gives the product of the two original width sums. -/
private theorem rectangles_area (horizontal vertical : List Interval) :
    PreparedBoxPartitions.sumCells Content.boxContent (rectangles horizontal vertical) =
      AxisPartition.widthSum horizontal * AxisPartition.widthSum vertical := by
  induction horizontal with
  | nil => change (0 : Coordinate) = 0 * _; ring1
  | cons first rest ih =>
      change PreparedBoxPartitions.sumCells Content.boxContent ((vertical.map (intervalBox first))
        ++ rectangles rest vertical) = _
      rw [PreparedBoxPartitions.sumCells_append, row_area, ih]
      change _ = ((first.upper - first.lower) + AxisPartition.widthSum rest) * _
      ring1

end Partition.PreparedRectangleCuts

set_option genInjectivity false in
/-- A cached rectangular partition containing the requested coordinate cuts.

The two axis partitions retain the original point bank; the exact Cartesian box
list and its quadratic count bound are cached alongside them. -/
public structure CutPartition (box : PreparedBoxPartitions.Box) (points : List PreparedBoxPartitions.Gaussian) where
  /-- The retained partition through all requested horizontal coordinates. -/ x : AxisPartition
    box.xLower box.xUpper (points.map fun point => point.re)
  /-- The retained partition through all requested vertical coordinates. -/ y : AxisPartition
    box.yLower box.yUpper (points.map fun point => point.im)
  /-- The cached Cartesian rectangle list. -/ boxes : List PreparedBoxPartitions.Box
  /-- The cache is exactly the Cartesian product of the retained axis intervals. -/ boxes_eq : boxes =
    Geometry.Rectangle.Partition.PreparedRectangleCuts.rectangles x.intervals y.intervals
  /-- The cached rectangle count. -/ count : Nat
  /-- The cached count equals the actual rectangle-list length. -/ count_eq : count = boxes.length
  /-- The rectangle count is bounded by the square of one more than the point count. -/ count_le : count ≤
    (points.length + 1) * (points.length + 1)

constructive_injectivity CutPartition

namespace CutPartition

variable {box : Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.Box} {points : List
  Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.Gaussian}

/-- Build and cache the Cartesian partition through the requested point
coordinates.

The original box must be proper. Each axis is sorted once and the rectangle
count is bounded by the square of one more than the point-list length. -/
@[expose] public def build (box : PreparedBoxPartitions.Box) (proper : box.Proper) (points : List
  PreparedBoxPartitions.Gaussian) : CutPartition box points :=
  let x := AxisPartition.build box.xLower box.xUpper proper.1 (points.map fun point => point.re)
  let y := AxisPartition.build box.yLower box.yUpper proper.2 (points.map fun point => point.im)
  let boxes := Geometry.Rectangle.Partition.PreparedRectangleCuts.rectangles x.intervals y.intervals
  { x := x
    y := y
    boxes := boxes
    boxes_eq := rfl
    count := x.count * y.count
    count_eq := by rw [Geometry.Rectangle.Partition.PreparedRectangleCuts.rectangles_length, x.count_eq, y.count_eq]
    count_le := by
      have bounded := Nat.mul_le_mul x.count_le y.count_le
      simpa only [Map.length_map] using bounded }

/-- Every cached rectangle has positive width and height.

Each cached rectangle comes from a pair of original proper intervals. Their two
strict endpoint inequalities certify that same box. -/
public theorem proper (partition : CutPartition box points) {inner : PreparedBoxPartitions.Box}
  (member : inner ∈ partition.boxes) : inner.Proper := by
  rw [partition.boxes_eq] at member
  obtain ⟨x, _, y, _, rfl⟩ := PreparedRectangleCuts.rectangles_mem.mp member
  exact ⟨x.ordered, y.ordered⟩

/-- Every cached rectangle refines the original box.

The selected rectangle retains intervals from the two original partitions.
Their closed frame bounds certify its endpoints against the supplied parent
box. -/
public theorem refines (partition : CutPartition box points) {inner : PreparedBoxPartitions.Box}
  (member : inner ∈ partition.boxes) : inner.Refines box := by
  rw [partition.boxes_eq] at member
  obtain ⟨x, xMember, y, yMember, rfl⟩ := PreparedRectangleCuts.rectangles_mem.mp member
  have horizontal := partition.x.interval_bounds xMember
  have vertical := partition.y.interval_bounds yMember
  exact ⟨horizontal.1, horizontal.2, vertical.1, vertical.2⟩

/-- The cached rectangles have pairwise separated interiors.

The stored intervals are the adjacent construction on strictly ordered cached
coordinates. Their original endpoint order forbids interior overlap. -/
public theorem separated (partition : CutPartition box points) : partition.boxes.Pairwise
  Rational.Box.InteriorSeparated := by
  rw [partition.boxes_eq]
  exact PreparedRectangleCuts.rectangles_separated _ _ partition.x.separated partition.y.separated

/-- The cached rectangle areas sum exactly to the original box area.

The Cartesian cache uses the retained axis width sums. Each equals its original
parent endpoint difference, yielding the exact parent box area. -/
public theorem area_eq (partition : CutPartition box points) : PreparedBoxPartitions.sumCells
  Content.boxContent partition.boxes =
    Content.boxContent box := by
  rw [partition.boxes_eq, PreparedRectangleCuts.rectangles_area, partition.x.widthSum_eq, partition.y.widthSum_eq]
  rfl

set_option genInjectivity false in
/-- An actual cached rectangle containing the specified point.

The record retains the actual selected box, its membership in the cached
Cartesian partition, and closed coordinate bounds for the supplied Gaussian
query. -/
public structure Located (partition : CutPartition box points) (point :
  PreparedBoxPartitions.Gaussian) where
  /-- The selected cached containing box. -/ box : PreparedBoxPartitions.Box
  /-- The selected box belongs to the partition. -/ member : box ∈ partition.boxes
  /-- The query lies inside the closed selected box. -/ inside : box.Contains point

constructive_injectivity Located

/-- Coverage is executable for every point, not just the finite cut bank.

The two original axis scans retain their selected intervals and containment
bounds. Their Cartesian box is a member of the original rectangle cache. -/
@[expose] public def locate (partition : CutPartition box points) (point
  : PreparedBoxPartitions.Gaussian) (inside : box.Contains point) :
  Located partition point :=
  let horizontal := partition.x.locate point.re ⟨inside.1, inside.2.1⟩
  let vertical := partition.y.locate point.im inside.2.2
  ⟨_root_.Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts.intervalBox horizontal.interval vertical.interval,
    by rw [partition.boxes_eq]; exact Geometry.Rectangle.Partition.PreparedRectangleCuts.rectangles_mem.mpr ⟨_,
      horizontal.member, _, vertical.member, rfl⟩,
    horizontal.inside.1, horizontal.inside.2, vertical.inside.1, vertical.inside.2⟩

end CutPartition

namespace Partition.PreparedRectangleCuts

/-- The four corner bits use the same orientation as the existing two
counterclockwise triangles, so the witness becomes a literal mesh vertex.

The two Boolean selections retain the original upper or lower coordinate. Their
orientation matches the existing two triangles of the same box. -/
@[expose] public def corner (box : PreparedBoxPartitions.Box) (xHigh yHigh : Bool) : Gaussian :=
  ⟨if xHigh then box.xUpper else box.xLower, if yHigh then box.yUpper else box.yLower⟩

end Partition.PreparedRectangleCuts

namespace CutPartition

variable {box : Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.Box} {points : List
  Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.Gaussian}

set_option genInjectivity false in
/-- An actual cached rectangle whose selected corner equals the requested point. -/
public structure Corner (partition : CutPartition box points) (point :
  PreparedBoxPartitions.Gaussian) where
  /-- The selected cached box with the requested corner. -/ box : PreparedBoxPartitions.Box
  /-- The selected box belongs to the partition. -/ member : box ∈ partition.boxes
  /-- Whether the corner uses the upper horizontal coordinate. -/ xHigh : Bool
  /-- Whether the corner uses the upper vertical coordinate. -/ yHigh : Bool
  /-- The selected corner equals the requested Gaussian rational point. -/ point_eq :
    Geometry.Rectangle.Partition.PreparedRectangleCuts.corner box xHigh yHigh = point

constructive_injectivity Corner

/-- A retained requested point is the selected corner of its cached rectangle.

The point supplies original horizontal and vertical cut occurrences. Their
retained endpoint witnesses select a cached box and the two bits reading that
exact point. -/
@[expose] public def atPoint (partition : CutPartition box points)
  (point : PreparedBoxPartitions.Gaussian) (member : point ∈ points) (inside : box.Contains point) :
    Corner partition point :=
  let horizontal := partition.x.endpoint point.re
    (partition.x.cut_mem (Map.mem_map.mpr ⟨point, member, rfl⟩) ⟨inside.1, inside.2.1⟩)
  let vertical := partition.y.endpoint point.im
    (partition.y.cut_mem (Map.mem_map.mpr ⟨point, member, rfl⟩) inside.2.2)
  ⟨_root_.Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts.intervalBox horizontal.interval vertical.interval,
    by rw [partition.boxes_eq]; exact Geometry.Rectangle.Partition.PreparedRectangleCuts.rectangles_mem.mpr ⟨_,
      horizontal.member, _, vertical.member, rfl⟩,
    horizontal.high, vertical.high, Data.Gaussian.Basic.ext horizontal.endpoint_eq vertical.endpoint_eq⟩

/-- Each corner of an input box appears in its two-triangle vertex list.

The four Boolean cases select existing vertices of the original two
counterclockwise triangles. Tail membership transports those same vertices
through earlier retained boxes. -/
private theorem corner_mem {boxes : List PreparedBoxPartitions.Box} {box : PreparedBoxPartitions.Box} (member : box ∈
  boxes) (xHigh yHigh : Bool) :
    PreparedRectangleCuts.corner box xHigh yHigh ∈ CoordinateTriangulation.triangleVertices
      (PreparedBoxTriangulation.boxTriangles boxes) := by
  induction boxes with
  | nil => cases member
  | cons head rest ih =>
      rcases Membership.mem_cons.mp member with rfl | member
      · cases xHigh <;> cases yHigh
        · exact List.Mem.head _
        · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head
            _)))))
        · exact List.Mem.tail _ (List.Mem.head _)
        · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih member))))))

/-- Every requested point inside the original box occurs in the retained triangle
vertex list.

The selected corner is an original cached rectangle corner equal to the
requested point. Its triangle-list membership transports that exact equality. -/
public theorem point_mem_vertices (partition : CutPartition box points) (point :
  PreparedBoxPartitions.Gaussian) (member : point ∈ points)
    (inside : box.Contains point) :
    point ∈ CoordinateTriangulation.triangleVertices (PreparedBoxTriangulation.boxTriangles partition.boxes) := by
  let found := partition.atPoint point member inside
  rw [← found.point_eq]
  exact corner_mem found.member found.xHigh found.yHigh

end CutPartition

end Purelib.Geometry.Rectangle
