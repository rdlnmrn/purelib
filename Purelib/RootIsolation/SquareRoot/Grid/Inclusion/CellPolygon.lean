module
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.AxisSpines
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CircuitSewing
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Sample

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-! The original cell boundary and the fine window boundary have the same
lifted ordered polygon, not merely the same sum of unlifted edge values. -/
namespace Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {original grid :
  ClearGrid polynomial ambient}
  (included : Geometry.Grid.Extension.CoordinateInclusion original grid)

/-- The four monotone sides retain their actual sheets and order; the top
and left sides use the existing certified reverse transport. -/
theorem cell_boundary_comparison (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈
  original.cells)
    (window : WindowBoundary.Window grid cell.box)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
      (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell member) (Geometry.Grid.ClearGrid.Cell.anchor_mem cell member))
      window.boundary := by
  let intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  let xEnds := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.vertical_ordered intervals.1
  let yEnds := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.horizontal_ordered intervals.2
  let x : Geometry.Grid.AxisWalks.IncreasingWalk original.xIntervals cell.horizontal.lower.coordinate
    cell.horizontal.upper.coordinate :=
    .cons cell.horizontal intervals.1 (.nil _)
  let y : Geometry.Grid.AxisWalks.IncreasingWalk original.yIntervals cell.vertical.lower.coordinate
    cell.vertical.upper.coordinate :=
    .cons cell.vertical intervals.2 (.nil _)
  let bottom := Geometry.Grid.Walks.Walk.horizontalIncreasing cell.vertical.lower yEnds.1 x
  let right := Geometry.Grid.Walks.Walk.verticalIncreasing cell.horizontal.upper xEnds.2 y
  let top := Geometry.Grid.Walks.Walk.horizontalIncreasing cell.vertical.upper yEnds.2 x
  let left := Geometry.Grid.Walks.Walk.verticalIncreasing cell.horizontal.lower xEnds.1 y
  have bottomEq := included.resplit_horizontalIncreasing cell.vertical.lower yEnds.1 x
    (Data.List.Map.mem_map_of_mem xEnds.2) window.x window.bottom
  have rightEq := included.resplit_verticalIncreasing cell.horizontal.upper xEnds.2 y
    (Data.List.Map.mem_map_of_mem yEnds.2) window.y window.right
  have topEq := included.resplit_horizontalIncreasing cell.vertical.upper yEnds.2 x
    (Data.List.Map.mem_map_of_mem xEnds.2) window.x window.top
  have leftEq := included.resplit_verticalIncreasing cell.horizontal.lower xEnds.1 y
    (Data.List.Map.mem_map_of_mem yEnds.2) window.y window.left
  have compared := included.resplit_rectangle edges vertices reference bottom right top left
    (Geometry.Grid.ClearGrid.Cell.anchor_mem cell member)
    ⟨Data.List.Map.mem_map_of_mem xEnds.2, Data.List.Map.mem_map_of_mem yEnds.1⟩
    ⟨Data.List.Map.mem_map_of_mem xEnds.1, Data.List.Map.mem_map_of_mem yEnds.2⟩
    ⟨Data.List.Map.mem_map_of_mem xEnds.2, Data.List.Map.mem_map_of_mem yEnds.2⟩
  change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
    (included.resplit (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell member)
      (Geometry.Grid.ClearGrid.Cell.anchor_mem cell member))
    ((included.resplit bottom _).append ((included.resplit right _).append
      ((included.resplit top _).reverse.append (included.resplit left _).reverse))) at compared
  rw [bottomEq, rightEq, topEq, leftEq] at compared
  exact compared

end Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion
