module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.VertexStar
public import Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

@[expose] public section

/-!
# Constructed side steps between grid cells incident at one vertex

Cells in a common row or column either coincide or share a full side. The
side witness retains literal reversed endpoints and the common vertex at one
end. Mixing the two adjacent-axis intervals stays in the same vertex star.
-/

namespace Purelib.Polynomial.Geometry.Grid.VertexCellSteps

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
  {point : Gaussian.Basic.Canonical}

set_option genInjectivity false in
/-- A grid cell retaining the specified point as a corner.

The cell and its membership witness refer to the original clear grid. -/
structure IncidentCell (grid : ClearGrid polynomial ambient) (point : Gaussian.Basic.Canonical) where
  /-- The retained grid cell. -/ cell : Geometry.Grid.ClearGrid.Cell polynomial ambient
  /-- The retained cell belongs to the original grid. -/ member : cell ∈ grid.cells
  /-- The specified point is a corner of the retained cell. -/ corner : cell.IsCorner point

constructive_injectivity IncidentCell

namespace IncidentCell

/-- Combine the horizontal interval of one incident cell with the vertical interval of another.

The resulting grid cell retains the common vertex as one of its corners. -/
def mix (first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point) :
  Geometry.Grid.VertexCellSteps.IncidentCell grid point :=
  ⟨⟨first.cell.horizontal, second.cell.vertical⟩,
    Data.List.Flatten.mem_flatMap.mpr ⟨first.cell.horizontal, (Geometry.Grid.CellBoundary.Cell.intervals_mem first.cell
      first.member).1,
      Data.List.Map.mem_map.mpr ⟨second.cell.vertical, (Geometry.Grid.CellBoundary.Cell.intervals_mem second.cell
        second.member).2, rfl⟩⟩,
    ⟨first.corner.1, second.corner.2⟩⟩

set_option genInjectivity false in
/-- The source side and target side are literal reversals; the common
vertex is an endpoint, not just a point somewhere on their supporting line. -/
structure Seam (first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point) where
  /-- The oriented side belonging to the first cell. -/ firstSide : Riemann.Meshes.GridLiftedDualSteps.GridSide
  /-- The oppositely oriented side belonging to the second cell. -/ secondSide :
    Riemann.Meshes.GridLiftedDualSteps.GridSide
  /-- The first side starts where the second side finishes. -/ start_eq : secondSide.start second.cell.box =
    firstSide.finish first.cell.box
  /-- The first side finishes where the second side starts. -/ finish_eq : secondSide.finish second.cell.box =
    firstSide.start first.cell.box
  /-- The common grid vertex is an endpoint of the seam. -/ at_vertex : firstSide.start first.cell.box = point ∨
    firstSide.finish first.cell.box = point

constructive_injectivity Seam

/-- Reverse the seam and exchange its two incident cells. -/
def Seam.reverse {first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point} (seam :
  Geometry.Grid.VertexCellSteps.IncidentCell.Seam first second) : Geometry.Grid.VertexCellSteps.IncidentCell.Seam second
  first :=
  ⟨seam.secondSide, seam.firstSide, seam.finish_eq.symm, seam.start_eq.symm, by
    rcases seam.at_vertex with atStart | atFinish
    · exact Or.inr (seam.finish_eq.trans atStart)
    · exact Or.inl (seam.start_eq.trans atFinish)⟩

set_option genInjectivity false in
/-- A certified move between cells incident to the same vertex.

The cells are either equal or connected by retained sides with opposite endpoint order. -/
inductive Step (first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point) where
  /-- The two incident cells are equal. -/ | same (equal : first.cell = second.cell)
  /-- The two incident cells meet along the retained oriented seam. -/ | across (seam :
    Geometry.Grid.VertexCellSteps.IncidentCell.Seam first second)

constructive_injectivity Step

/-- Reverse a move between two cells incident to the same vertex. -/
def Step.reverse {first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point} :
  Geometry.Grid.VertexCellSteps.IncidentCell.Step first second → Geometry.Grid.VertexCellSteps.IncidentCell.Step second
  first
  | .same equal => .same equal.symm
  | .across seam => .across seam.reverse

/-- At the specified imaginary coordinate, the vertex lies on a horizontal endpoint of the incident cell. -/
public theorem horizontal_at (first : Geometry.Grid.VertexCellSteps.IncidentCell grid point) {y : Fraction.Rational}
  (equal : y = point.im) :
    Gaussian.Components.Basic.point first.cell.box.xLower y = point ∨ Gaussian.Components.Basic.point
      first.cell.box.xUpper y = point := by
  rcases first.corner.1 with lower | upper
  · exact Or.inl (congrArg₂ Gaussian.Components.Basic.point lower equal)
  · exact Or.inr (congrArg₂ Gaussian.Components.Basic.point upper equal)

/-- At the specified real coordinate, the vertex lies on a vertical endpoint of the incident cell. -/
public theorem vertical_at (first : Geometry.Grid.VertexCellSteps.IncidentCell grid point) {x : Fraction.Rational}
  (equal : x = point.re) :
    Gaussian.Components.Basic.point x first.cell.box.yLower = point ∨ Gaussian.Components.Basic.point x
      first.cell.box.yUpper = point := by
  rcases first.corner.2 with lower | upper
  · exact Or.inl (congrArg₂ Gaussian.Components.Basic.point equal lower)
  · exact Or.inr (congrArg₂ Gaussian.Components.Basic.point equal upper)

/-- The two cells use the same horizontal interval. Endpoint uniqueness
decides coincidence; otherwise their top/bottom sides meet at the vertex. -/
def alongColumn (first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point)
    (horizontal : first.cell.horizontal = second.cell.horizontal) : Geometry.Grid.VertexCellSteps.IncidentCell.Step
      first second :=
  if lowerEqual : first.cell.vertical.lower.coordinate = second.cell.vertical.lower.coordinate then
    .same (congrArg₂ Geometry.Grid.ClearGrid.Cell.mk horizontal (Geometry.Grid.AxisNeighbors.eq_of_lower
      grid.horizontal_ordered
      (Geometry.Grid.CellBoundary.Cell.intervals_mem first.cell first.member).2
        (Geometry.Grid.CellBoundary.Cell.intervals_mem second.cell second.member).2 lowerEqual))
  else if atLower : first.cell.box.yLower = point.im then
    let atUpper : second.cell.box.yUpper = point.im := second.corner.2.resolve_left
      (fun equal => lowerEqual (atLower.trans equal.symm))
    .across ⟨.bottom, .top,
      congrArg₂ Gaussian.Components.Basic.point (congrArg (fun interval => interval.upper.coordinate) horizontal.symm)
        (atUpper.trans atLower.symm),
      congrArg₂ Gaussian.Components.Basic.point (congrArg (fun interval => interval.lower.coordinate) horizontal.symm)
        (atUpper.trans atLower.symm),
      first.horizontal_at atLower⟩
  else
    let atUpper := first.corner.2.resolve_left atLower
    let nextLower : second.cell.box.yLower = point.im := second.corner.2.resolve_right (fun equal => by
      have intervals := Geometry.Grid.AxisNeighbors.eq_of_upper grid.horizontal_ordered
        (Geometry.Grid.CellBoundary.Cell.intervals_mem first.cell first.member).2
          (Geometry.Grid.CellBoundary.Cell.intervals_mem second.cell second.member).2 (atUpper.trans equal.symm)
      exact lowerEqual (congrArg (fun interval => interval.lower.coordinate) intervals))
    .across ⟨.top, .bottom,
      congrArg₂ Gaussian.Components.Basic.point (congrArg (fun interval => interval.lower.coordinate) horizontal.symm)
        (nextLower.trans atUpper.symm),
      congrArg₂ Gaussian.Components.Basic.point (congrArg (fun interval => interval.upper.coordinate) horizontal.symm)
        (nextLower.trans atUpper.symm),
      (first.horizontal_at atUpper).symm⟩

/-- The corresponding left/right side step for a common vertical interval. -/
def alongRow (first second : Geometry.Grid.VertexCellSteps.IncidentCell grid point)
    (vertical : first.cell.vertical = second.cell.vertical) : Geometry.Grid.VertexCellSteps.IncidentCell.Step first
      second :=
  if lowerEqual : first.cell.horizontal.lower.coordinate = second.cell.horizontal.lower.coordinate then
    .same (congrArg₂ Geometry.Grid.ClearGrid.Cell.mk (Geometry.Grid.AxisNeighbors.eq_of_lower grid.vertical_ordered
      (Geometry.Grid.CellBoundary.Cell.intervals_mem first.cell first.member).1
        (Geometry.Grid.CellBoundary.Cell.intervals_mem second.cell second.member).1 lowerEqual) vertical)
  else if atLower : first.cell.box.xLower = point.re then
    let atUpper : second.cell.box.xUpper = point.re := second.corner.1.resolve_left
      (fun equal => lowerEqual (atLower.trans equal.symm))
    .across ⟨.left, .right,
      congrArg₂ Gaussian.Components.Basic.point (atUpper.trans atLower.symm) (congrArg (fun interval =>
        interval.lower.coordinate) vertical.symm),
      congrArg₂ Gaussian.Components.Basic.point (atUpper.trans atLower.symm) (congrArg (fun interval =>
        interval.upper.coordinate) vertical.symm),
      (first.vertical_at atLower).symm⟩
  else
    let atUpper := first.corner.1.resolve_left atLower
    let nextLower : second.cell.box.xLower = point.re := second.corner.1.resolve_right (fun equal => by
      have intervals := Geometry.Grid.AxisNeighbors.eq_of_upper grid.vertical_ordered
        (Geometry.Grid.CellBoundary.Cell.intervals_mem first.cell first.member).1
          (Geometry.Grid.CellBoundary.Cell.intervals_mem second.cell second.member).1 (atUpper.trans equal.symm)
      exact lowerEqual (congrArg (fun interval => interval.lower.coordinate) intervals))
    .across ⟨.right, .left,
      congrArg₂ Gaussian.Components.Basic.point (nextLower.trans atUpper.symm) (congrArg (fun interval =>
        interval.upper.coordinate) vertical.symm),
      congrArg₂ Gaussian.Components.Basic.point (nextLower.trans atUpper.symm) (congrArg (fun interval =>
        interval.lower.coordinate) vertical.symm),
      first.vertical_at atUpper⟩

end IncidentCell

end Purelib.Polynomial.Geometry.Grid.VertexCellSteps
