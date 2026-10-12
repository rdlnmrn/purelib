module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.AxisSpines
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-! Splitting on the same grid preserves the actual lifted walk, its sheet,
and its full increment polygon. This permits reuse of the resplit compiler. -/

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)

include reference

/-- Resplitting one original grid edge through the self-inclusion preserves its retained chain comparison on every
sheet. -/
private theorem self_edge : {start finish : Gaussian.Basic.Canonical} → (edge : Geometry.Grid.Walks.Edge grid start
  finish) →
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      ((Geometry.Grid.Extension.CoordinateInclusion.refl grid).resplit (.cons edge (.nil _)) edge.vertices.2) (.cons
        edge (.nil _))
  | _, _, .horizontal interval adjacent line member => by
      let axis : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals interval.lower.coordinate
        interval.upper.coordinate :=
        .cons interval adjacent (.nil _)
      have same := (Geometry.Grid.Extension.CoordinateInclusion.refl grid).resplit_horizontalIncreasing line member axis
        (List.Map.mem_map_of_mem (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.vertical_ordered adjacent).2)
        axis ⟨line, member, rfl⟩
      exact SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq same
  | _, _, .vertical interval adjacent line member => by
      let axis : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals interval.lower.coordinate
        interval.upper.coordinate :=
        .cons interval adjacent (.nil _)
      have same := (Geometry.Grid.Extension.CoordinateInclusion.refl grid).resplit_verticalIncreasing line member axis
        (List.Map.mem_map_of_mem (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered adjacent).2)
        axis ⟨line, member, rfl⟩
      exact SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq same
  | _, _, .reverse edge =>
      ((Geometry.Grid.Extension.CoordinateInclusion.refl grid).resplit_reverse edges vertices reference
        (.cons edge (.nil _)) edge.vertices.1 edge.vertices.2).trans
          (AxisChainCoherence.RootEdgeBank.ChainComparison.reverse
            reference (self_edge edge))

/-- The self-inclusion is used only to reuse already certified compiler
requests; it changes neither the geometric walk nor its area owner. -/
theorem self_resplit_comparison {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start
  finish)
    (member : FromStates.ContainsVertex grid finish) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      ((Geometry.Grid.Extension.CoordinateInclusion.refl grid).resplit walk member) walk := by
  induction walk with
  | nil => exact SquareRoot.Grid.RootEdgeBank.ChainComparison.refl _
  | cons edge tail ih =>
      change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
        ((Geometry.Grid.Extension.CoordinateInclusion.refl grid).resplit ((Geometry.Grid.Walks.Walk.cons edge (.nil
          _)).append tail) member)
        ((Geometry.Grid.Walks.Walk.cons edge (.nil _)).append tail)
      rw [Geometry.Grid.Extension.CoordinateInclusion.resplit_append _ _ _ edge.vertices.2 member]
      exact (self_edge edges vertices reference edge).append (ih member)

end Purelib.Polynomial.Geometry.Grid.ClearGrid
