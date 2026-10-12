module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Incidence
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Separation

public section

/-!
# Complete finite vertex stars of the actual clear-line grid

The product of the two certified axis neighborhoods contains every incident
cell, including boundary cells, and no unrelated rectangle. There are at most
four. Every entry retains the original line-clearance payloads; no root or
clearance computation is performed while constructing this finite star.
-/

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.Polynomial.Geometry.Grid.AxisNeighbors
  (eq_of_lower Neighbors neighbors)
open Purelib.Polynomial.Geometry.Grid.Incidence.Interval (coordinate_side)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

namespace Cell

/-- A point has one of the cell's two endpoint coordinates in each direction. -/
@[expose] def IsCorner (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (point : Gaussian.Basic.Canonical) :
  Prop :=
  (cell.box.xLower = point.re ∨ cell.box.xUpper = point.re) ∧
    (cell.box.yLower = point.im ∨ cell.box.yUpper = point.im)

namespace IsCorner

/-- Every corner belongs to the cell's closed box. -/
theorem contains {cell : Geometry.Grid.ClearGrid.Cell polynomial ambient} {point : Gaussian.Basic.Canonical}
    (corner : cell.IsCorner point) : cell.box.Contains point := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases corner.1 with lower | upper
    · exact lower.le
    · exact cell.box.x_valid.trans_eq upper
  · rcases corner.1 with lower | upper
    · exact lower.symm.trans_le cell.box.x_valid
    · exact upper.symm.le
  · rcases corner.2 with lower | upper
    · exact lower.le
    · exact cell.box.y_valid.trans_eq upper
  · rcases corner.2 with lower | upper
    · exact lower.symm.trans_le cell.box.y_valid
    · exact upper.symm.le

end IsCorner

end Cell

section Grid

variable {grid : ClearGrid polynomial ambient}

/-- Two cells of the same grid with equal lower-left anchors are identical. -/
theorem cell_eq_of_anchor {first second : Geometry.Grid.ClearGrid.Cell polynomial ambient}
    (firstMember : first ∈ grid.cells) (secondMember : second ∈ grid.cells)
    (equal : first.box.anchor = second.box.anchor) : first = second :=
  congrArg₂ Geometry.Grid.ClearGrid.Cell.mk
    (Geometry.Grid.AxisNeighbors.eq_of_lower grid.vertical_ordered (Geometry.Grid.CellBoundary.Cell.intervals_mem first
      firstMember).1
      (Geometry.Grid.CellBoundary.Cell.intervals_mem second secondMember).1 (congrArg (fun point :
        Gaussian.Basic.Canonical => point.re) equal))
    (Geometry.Grid.AxisNeighbors.eq_of_lower grid.horizontal_ordered (Geometry.Grid.CellBoundary.Cell.intervals_mem
      first firstMember).2
      (Geometry.Grid.CellBoundary.Cell.intervals_mem second secondMember).2 (congrArg (fun point :
        Gaussian.Basic.Canonical => point.im) equal))

open Purelib.Polynomial.Geometry.Grid.Incidence.Interval in
/-- A retained grid vertex cannot lie strictly between consecutive lines.
Thus incidence expressed by closed containment is exactly corner incidence. -/
theorem corner_of_contains {cell : Geometry.Grid.ClearGrid.Cell polynomial ambient} (member : cell ∈ grid.cells)
    {point : Gaussian.Basic.Canonical} (onGrid : FromStates.ContainsVertex grid point) (inside :
      cell.box.Contains point) : cell.IsCorner point := by
  have intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  constructor
  · rcases coordinate_side _ grid.vertical_ordered intervals.1 onGrid.1 with before | after
    · exact Or.inl (le_antisymm inside.1 before)
    · exact Or.inr (le_antisymm after inside.2.1)
  · rcases coordinate_side _ grid.horizontal_ordered intervals.2 onGrid.2 with before | after
    · exact Or.inl (le_antisymm inside.2.2.1 before)
    · exact Or.inr (le_antisymm after inside.2.2.2)

set_option genInjectivity false in
/-- The explicit finite collection of cells incident to a retained grid vertex.

The two certified axis neighborhoods and their Cartesian product are retained with an exact list identity. -/
structure VertexStar (grid : ClearGrid polynomial ambient) (point : Gaussian.Basic.Canonical) where
  /-- The displayed point is a vertex of the retained grid. -/ onGrid : FromStates.ContainsVertex
    grid point
  /-- The certified adjacent vertical-line intervals at the vertex abscissa. -/ x :
    Geometry.Grid.AxisNeighbors.Neighbors grid.vertical grid.vertical_ordered point.re
  /-- The certified adjacent horizontal-line intervals at the vertex ordinate. -/ y :
    Geometry.Grid.AxisNeighbors.Neighbors grid.horizontal grid.horizontal_ordered point.im
  /-- The retained finite list of incident cells. -/ cells : List (Geometry.Grid.ClearGrid.Cell polynomial ambient)
  /-- The incident-cell list is exactly the product of the two retained interval neighborhoods. -/ cells_eq : cells =
    x.intervals.flatMap fun horizontal => y.intervals.map fun vertical => ⟨horizontal, vertical⟩

constructive_injectivity VertexStar

namespace VertexStar

variable {point : Gaussian.Basic.Canonical}

/-- Compute both axis neighborhoods and their finite cell product.

The construction reuses the retained line-clearance payloads and the supplied vertex-membership certificate. -/
@[expose] def build (grid : ClearGrid polynomial ambient) (point : Gaussian.Basic.Canonical) (onGrid
  : FromStates.ContainsVertex grid point) : VertexStar grid point :=
  let x := Geometry.Grid.AxisNeighbors.neighbors point.re grid.vertical grid.vertical_ordered onGrid.1
  let y := Geometry.Grid.AxisNeighbors.neighbors point.im grid.horizontal grid.horizontal_ordered onGrid.2
  ⟨onGrid, x, y, x.intervals.flatMap (fun horizontal => y.intervals.map fun vertical => ⟨horizontal, vertical⟩), rfl⟩

section
open Purelib.Polynomial.Geometry.Grid.ClearGrid.VertexStar
/-- Every cell in a vertex star belongs to its original grid. -/
theorem member (star : VertexStar grid point) {cell : Geometry.Grid.ClearGrid.Cell
  polynomial ambient} (member : cell ∈ star.cells) : cell ∈ grid.cells := open Purelib in by
  rw [star.cells_eq] at member
  obtain ⟨horizontal, horizontalMember, member⟩ := Data.List.Flatten.mem_flatMap.mp member
  obtain ⟨vertical, verticalMember, equal⟩ := Data.List.Map.mem_map.mp member
  exact Data.List.Flatten.mem_flatMap.mpr ⟨horizontal, star.x.member horizontalMember,
    Data.List.Map.mem_map.mpr ⟨vertical, star.y.member verticalMember, equal⟩⟩

/-- Every cell in a vertex star has the retained point as a corner. -/
theorem corner (star : VertexStar grid point) {cell : Geometry.Grid.ClearGrid.Cell
  polynomial ambient} (member : cell ∈ star.cells) : cell.IsCorner point := open Purelib in by
  rw [star.cells_eq] at member
  obtain ⟨horizontal, horizontalMember, member⟩ := Data.List.Flatten.mem_flatMap.mp member
  obtain ⟨vertical, verticalMember, equal⟩ := Data.List.Map.mem_map.mp member
  rw [← equal]
  exact ⟨star.x.endpoint horizontalMember, star.y.endpoint verticalMember⟩

/-- Every cell in a vertex star contains the retained point. -/
theorem contains (star : VertexStar grid point) {cell : Geometry.Grid.ClearGrid.Cell
  polynomial ambient} (member : cell ∈ star.cells) :
    cell.box.Contains point := (star.corner member).contains

/-- Every original grid cell having the retained vertex as a corner occurs in its star. -/
theorem covers_corner (star : VertexStar grid point) {cell : Geometry.Grid.ClearGrid.Cell
  polynomial ambient}
    (member : cell ∈ grid.cells) (corner : cell.IsCorner point) : cell ∈ star.cells := open Purelib in by
  rw [star.cells_eq]
  have intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  exact Data.List.Flatten.mem_flatMap.mpr ⟨cell.horizontal, star.x.covers intervals.1 corner.1,
    Data.List.Map.mem_map.mpr ⟨cell.vertical, star.y.covers intervals.2 corner.2, rfl⟩⟩

/-- Every original grid cell containing the retained grid vertex occurs in its star. -/
theorem covers (star : VertexStar grid point) {cell : Geometry.Grid.ClearGrid.Cell
  polynomial ambient}
    (member : cell ∈ grid.cells) (inside : cell.box.Contains point) : cell ∈ star.cells :=
  star.covers_corner member (corner_of_contains member star.onGrid inside)

end

/-- The star size is the product of its two axis-neighborhood sizes.

The original cached cell equation identifies the Cartesian product of the two retained neighborhoods. The structural
list-product length law counts those exact ordered occurrences. -/
theorem length_eq_product (star : VertexStar grid point) :
    star.cells.length = star.x.intervals.length * star.y.intervals.length := by
  rw [star.cells_eq]
  exact List.Flatten.length_flatMap_map star.x.intervals star.y.intervals Cell.mk

/-- A retained grid vertex has at most four incident cells. -/
theorem length_le_four (star : VertexStar grid point) : star.cells.length ≤ 4 := by
  rw [star.length_eq_product]
  exact Nat.mul_le_mul star.x.length_le_two star.y.length_le_two

open Purelib.Polynomial.Geometry.Grid.ClearGrid.VertexStar in
/-- Cells in one column with ordered vertical intervals have pairwise separated interiors. -/
private theorem column_pairwise
    (horizontal : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (verticals : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial
      := polynomial) (ambient := ambient))))
    (ordered : verticals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) :
    (verticals.map (fun vertical => (⟨horizontal, vertical⟩ : Geometry.Grid.ClearGrid.Cell polynomial
      ambient))).Pairwise
      (fun first second => first.box.InteriorSeparated second.box) := open Purelib in by
  induction verticals with
  | nil => exact .nil
  | cons vertical rest ih =>
      refine .cons ?_ (ih (List.pairwise_cons.mp ordered).2)
      intro cell member
      obtain ⟨next, nextMember, equal⟩ := Data.List.Map.mem_map.mp member
      rw [← equal]
      exact Geometry.Grid.ClearGrid.Cell.vertical_separated _ _ ((List.pairwise_cons.mp ordered).1 next nextMember)

/-- Cells formed from two ordered interval lists have pairwise separated interiors.

Each retained horizontal interval contributes its unchanged vertical column. Structural concatenation preserves the
displayed order; the original interval ordering separates each earlier column from every later one. -/
private theorem product_pairwise
    (horizontals : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial
      := polynomial) (ambient := ambient))))
    (verticals : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial
      := polynomial) (ambient := ambient))))
    (horizontalOrdered : horizontals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) (verticalOrdered :
      verticals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) :
    (horizontals.flatMap fun horizontal => verticals.map fun vertical => (⟨horizontal, vertical⟩ :
      Geometry.Grid.ClearGrid.Cell polynomial ambient)).Pairwise
      (fun first second => first.box.InteriorSeparated second.box) := open Purelib in by
  induction horizontals with
  | nil => exact .nil
  | cons horizontal rest ih =>
      rw [List.Flatten.flatMap_cons]
      refine Data.List.Pairwise.pairwise_append (column_pairwise horizontal
        verticals verticalOrdered)
        (ih (List.pairwise_cons.mp horizontalOrdered).2) ?_
      intro first firstMember second secondMember
      obtain ⟨firstVertical, _, firstEq⟩ := Data.List.Map.mem_map.mp firstMember
      obtain ⟨secondHorizontal, secondHorizontalMember, secondMember⟩ := Data.List.Flatten.mem_flatMap.mp secondMember
      obtain ⟨secondVertical, _, secondEq⟩ := Data.List.Map.mem_map.mp secondMember
      rw [← firstEq, ← secondEq]
      exact Geometry.Grid.ClearGrid.Cell.horizontal_separated _ _ ((List.pairwise_cons.mp horizontalOrdered).1
        secondHorizontal secondHorizontalMember)

/-- The incident cells in a vertex star have pairwise separated interiors. -/
theorem pairwise (star : VertexStar grid point) :
    star.cells.Pairwise (fun first second => first.box.InteriorSeparated second.box) := by
  rw [star.cells_eq]
  exact product_pairwise _ _ star.x.pairwise star.y.pairwise

/-- The vertex-star cell list contains no duplicate cells. -/
theorem nodup (star : VertexStar grid point) : star.cells.Nodup := by
  refine List.Pairwise.imp (fun {first second} apart same => ?_) star.pairwise
  subst second
  rcases apart with before | after | below | above
  · exact not_lt_of_ge before first.box_proper.1
  · exact not_lt_of_ge after first.box_proper.1
  · exact not_lt_of_ge below first.box_proper.2
  · exact not_lt_of_ge above first.box_proper.2

end VertexStar
end Grid

end Purelib.Polynomial.Geometry.Grid.ClearGrid
