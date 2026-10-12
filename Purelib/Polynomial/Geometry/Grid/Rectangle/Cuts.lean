module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Exact rectangular restriction to an existing clear grid

Cut a proper rectangle at the coordinates of an already retained grid. The
existing finite partition preserves area and excludes every grid line from
the interior of each piece. Consequently any grid cell containing an
interior point of a piece contains the whole piece. No new grid, clearance
calculation, or successful coverage check is required.
-/

namespace Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib
open Purelib.Polynomial
open Purelib.Data.List

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Axis coordinates are copied from the actual grid, including its frame. The
unused coordinate lies on the rectangle boundary and creates no cut.

The original vertical coordinates are followed by the original horizontal
coordinates. Each extra coordinate is paired with the supplied rectangle
boundary, preserving the finite cut order. -/
@[expose] public def cutPoints (grid : ClearGrid polynomial ambient) (box : Box) :
  List Gaussian :=
  (grid.vertical.map fun line => ⟨line.coordinate, box.yLower⟩) ++
    (grid.horizontal.map fun line => ⟨box.xLower, line.coordinate⟩)

/-- The exact prepared rectangle partition at coordinates copied from the retained
grid.

The underlying prepared partition uses the supplied box and exactly the
displayed cutPoints list. The alias preserves all cached axis and rectangle
identities. -/
public abbrev Partition (grid : ClearGrid polynomial ambient) (box : Box) :=
  Geometry.Rectangle.CutPartition box (Geometry.Grid.Rectangle.Cuts.cutPoints grid box)

/-- The Gaussian point given by the two rational coordinate midpoints of a box.

Both coordinates use the original midpoint operation on the stored box
endpoints. The resulting Gaussian point belongs to that same box. -/
@[expose] public def center (box : Box) : Gaussian :=
  ⟨Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint box.xLower box.xUpper,
    Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint box.yLower box.yUpper⟩

/-- The midpoint lies strictly inside a proper box.

The original box has strict horizontal and vertical endpoint order. Its four
half-interval bounds place the retained midpoint strictly inside both
coordinates. -/
public theorem center_strict {box : Box} (proper : box.Proper) : box.StrictContains
  (Geometry.Grid.Rectangle.Cuts.center box) :=
  ⟨Geometry.Rectangle.Partition.PreparedBoxPartitions.half_proper proper.1 false,
    Geometry.Rectangle.Partition.PreparedBoxPartitions.half_proper proper.1 true,
    Geometry.Rectangle.Partition.PreparedBoxPartitions.half_proper proper.2 false,
    Geometry.Rectangle.Partition.PreparedBoxPartitions.half_proper proper.2 true⟩

/-- The midpoint belongs to a proper box.

The strict midpoint certificate supplies all four weak bounds. The displayed
point and original box remain unchanged. -/
public theorem center_inside {box : Box} (proper : box.Proper) : box.Contains
  (Geometry.Grid.Rectangle.Cuts.center box) :=
  let inside := Geometry.Grid.Rectangle.Cuts.center_strict proper
  ⟨inside.1.le, inside.2.1.le, inside.2.2.1.le, inside.2.2.2.le⟩

namespace Partition

variable {grid : ClearGrid polynomial ambient} {box : Box}

/-- Construct the finite rectangle partition using the retained grid's coordinate
cuts.

The original proper rectangle and displayed cut list determine the retained
pieces and their partition proofs. -/
@[expose] public def build (grid : ClearGrid polynomial ambient) (box : Box) (proper
  : box.Proper) : Geometry.Grid.Rectangle.Cuts.Partition grid box :=
  Geometry.Rectangle.CutPartition.build box proper (Geometry.Grid.Rectangle.Cuts.cutPoints
    grid box)

/-- Every retained vertical grid line lies outside the open horizontal interior of
each partition piece.

The selected original vertical line contributes its coordinate to the retained
cut bank. The axis partition places that occurrence outside each cached
horizontal interval interior. -/
public theorem vertical_outside (partition : Geometry.Grid.Rectangle.Cuts.Partition grid box) {small :
  Box} (member : small ∈ partition.boxes)
    {line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient} (present : line ∈ grid.vertical) :
    line.coordinate ≤ small.xLower ∨ small.xUpper ≤ line.coordinate := by
  rw [partition.boxes_eq] at member
  obtain ⟨x, xMember, rowMember⟩ := Data.List.Flatten.mem_flatMap.mp member
  obtain ⟨y, _, rfl⟩ := Data.List.Map.mem_map.mp rowMember
  apply partition.x.cut_outside xMember
  exact Data.List.Map.mem_map.mpr ⟨⟨line.coordinate, box.yLower⟩,
    List.mem_append_left _ (Data.List.Map.mem_map.mpr ⟨line, present, rfl⟩), rfl⟩

/-- Every retained horizontal grid line lies outside the open vertical interior of
each partition piece.

The selected original horizontal line contributes its coordinate to the
retained cut bank. The axis partition places that occurrence outside each
cached vertical interval interior. -/
public theorem horizontal_outside (partition : Geometry.Grid.Rectangle.Cuts.Partition grid box) {small :
  Box} (member : small ∈ partition.boxes)
    {line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient} (present : line ∈ grid.horizontal) :
    line.coordinate ≤ small.yLower ∨ small.yUpper ≤ line.coordinate := by
  rw [partition.boxes_eq] at member
  obtain ⟨x, _, rowMember⟩ := Data.List.Flatten.mem_flatMap.mp member
  obtain ⟨y, yMember, rfl⟩ := Data.List.Map.mem_map.mp rowMember
  apply partition.y.cut_outside yMember
  exact Data.List.Map.mem_map.mpr ⟨⟨box.xLower, line.coordinate⟩,
    List.mem_append_right _ (Data.List.Map.mem_map.mpr ⟨line, present, rfl⟩), rfl⟩

/-- An interval containing an interior query contains the whole inner interval when
both of its endpoints lie outside that inner interval's open interior.

Both outer endpoints lie outside the inner interval interior while containing
its strict interior query. Those inequalities force the displayed endpoint
refinement. -/
private theorem interval_refines {lower upper first last point : Fraction.Rational}
    (inside : lower < point ∧ point < upper) (contains : first ≤ point ∧ point ≤ last)
    (firstOutside : first ≤ lower ∨ upper ≤ first) (lastOutside : last ≤ lower ∨ upper ≤ last) :
    first ≤ lower ∧ upper ≤ last := by
  constructor
  · rcases firstOutside with bound | bound
    · exact bound
    · exact (not_lt_of_ge (bound.trans contains.1) inside.2).elim
  · rcases lastOutside with bound | bound
    · exact (not_lt_of_ge (contains.2.trans bound) inside.1).elim
    · exact bound

/-- Membership refers to the original Cartesian grid, not a replacement rectangle
with merely equal area. Interior point location supplies all four containment
inequalities because every original side occurs among the cuts. -/
public theorem refines_cell (partition : Geometry.Grid.Rectangle.Cuts.Partition grid box) {small : Box}
  (member : small ∈ partition.boxes)
    {cell : Geometry.Grid.ClearGrid.Cell polynomial ambient} (cellMember : cell ∈ grid.cells) {point :
      Gaussian.Basic.Canonical}
    (inside : small.StrictContains point) (contains : cell.box.Contains point) : small.Refines cell.box := by
  obtain ⟨x, xMember, rowMember⟩ := Data.List.Flatten.mem_flatMap.mp cellMember
  obtain ⟨y, yMember, equal⟩ := Data.List.Map.mem_map.mp rowMember
  subst cell
  have horizontal := Geometry.Grid.ClearGrid.Interval.endpoints_mem grid.vertical grid.vertical_ordered xMember
  have vertical := Geometry.Grid.ClearGrid.Interval.endpoints_mem grid.horizontal grid.horizontal_ordered yMember
  have xBounds := Geometry.Grid.Rectangle.Cuts.Partition.interval_refines ⟨inside.1, inside.2.1⟩ ⟨contains.1,
    contains.2.1⟩
    (partition.vertical_outside member horizontal.1) (partition.vertical_outside member horizontal.2)
  have yBounds := Geometry.Grid.Rectangle.Cuts.Partition.interval_refines inside.2.2 contains.2.2
    (partition.horizontal_outside member vertical.1) (partition.horizontal_outside member vertical.2)
  exact ⟨xBounds.1, xBounds.2, yBounds.1, yBounds.2⟩

end Partition
end Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
