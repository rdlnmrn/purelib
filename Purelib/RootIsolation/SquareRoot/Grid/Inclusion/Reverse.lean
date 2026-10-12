module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine VerticalLine)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank (ChainComparison)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-! Subdivision preserves reversed connectors on both lifted sheets. The
comparison retains the finite indexed words up to certified retracing. -/

namespace Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
  (horizontalWalk_decreasing horizontalWalk_increasing verticalWalk_decreasing verticalWalk_increasing)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)

include reference

/-- Resplitting a reversed horizontal grid walk compares to reversing its original resplitting. -/
private theorem horizontal_reverse (start finish y : Purelib.Data.Rat.Fraction.Rational)
    (first : start ∈ grid.vertical.map VerticalLine.coordinate)
    (last : finish ∈ grid.vertical.map VerticalLine.coordinate)
    (fixed : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    ChainComparison edges vertices
      (Geometry.Grid.Walks.horizontalWalk grid finish start y last first fixed)
      (Geometry.Grid.Walks.horizontalWalk grid start finish y first last fixed).reverse := by
  let line := Geometry.Grid.AxisWalks.lookup y grid.horizontal fixed
  by_cases ordered : start ≤ finish
  · let axis := Geometry.Grid.AxisWalks.increasing start finish grid.vertical grid.vertical_ordered first last ordered
    rw [AxisChainCoherence.horizontalWalk_decreasing axis line,
      AxisChainCoherence.horizontalWalk_increasing axis line]
    exact .refl _
  · let axis := Geometry.Grid.AxisWalks.increasing finish start grid.vertical grid.vertical_ordered last first
      (le_of_not_ge ordered)
    rw [AxisChainCoherence.horizontalWalk_increasing axis line,
      AxisChainCoherence.horizontalWalk_decreasing axis line]
    exact (AxisChainCoherence.RootEdgeBank.ChainComparison.reverse_reverse reference _).symm

/-- Resplitting a reversed vertical grid walk compares to reversing its original resplitting. -/
private theorem vertical_reverse (x start finish : Purelib.Data.Rat.Fraction.Rational)
    (fixed : x ∈ grid.vertical.map VerticalLine.coordinate)
    (first : start ∈ grid.horizontal.map HorizontalLine.coordinate)
    (last : finish ∈ grid.horizontal.map HorizontalLine.coordinate) :
    ChainComparison edges vertices
      (Geometry.Grid.Walks.verticalWalk grid x finish start fixed last first)
      (Geometry.Grid.Walks.verticalWalk grid x start finish fixed first last).reverse := by
  let line := Geometry.Grid.AxisWalks.lookup x grid.vertical fixed
  by_cases ordered : start ≤ finish
  · let axis := Geometry.Grid.AxisWalks.increasing start finish grid.horizontal grid.horizontal_ordered first last
      ordered
    rw [AxisChainCoherence.verticalWalk_decreasing axis line,
      AxisChainCoherence.verticalWalk_increasing axis line]
    exact .refl _
  · let axis := Geometry.Grid.AxisWalks.increasing finish start grid.horizontal grid.horizontal_ordered last first
      (le_of_not_ge ordered)
    rw [AxisChainCoherence.verticalWalk_increasing axis line,
      AxisChainCoherence.verticalWalk_decreasing axis line]
    exact (AxisChainCoherence.RootEdgeBank.ChainComparison.reverse_reverse reference _).symm

/-- Reversing an original affine grid segment commutes with its retained coordinate split up to chain comparison. -/
private theorem split_reverse {pathAmbient : Box} {start finish : Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial pathAmbient start finish)
    (first : FromStates.ContainsVertex grid start) (last :
      FromStates.ContainsVertex grid finish) :
    ChainComparison edges vertices
      (Geometry.Grid.Walks.splitSegment grid (Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse
        segment) last first) (Geometry.Grid.Walks.splitSegment grid segment first last).reverse := by
  cases segment with
  | horizontal => exact horizontal_reverse edges vertices reference _ _ _ _ _ _
  | vertical => exact vertical_reverse edges vertices reference _ _ _ _ _ _

namespace CoordinateInclusion

variable {original : ClearGrid polynomial ambient} (included :
  Geometry.Grid.Extension.CoordinateInclusion original grid)

/-- Resplitting a reversed retained grid walk compares to the reverse of its original resplitting. -/
theorem resplit_reverse {start finish : Canonical} (walk : Walk original start
  finish)
    (first : FromStates.ContainsVertex original start) (last :
      FromStates.ContainsVertex original finish) :
    ChainComparison edges vertices
      (included.resplit walk.reverse first) (included.resplit walk last).reverse := by
  induction walk with
  | nil => exact .refl _
  | @cons start middle finish edge tail ih =>
      have reversed : (Walk.cons edge tail).reverse = tail.reverse.append (.cons edge.reverse (.nil
        start)) :=
        Walk.reverseOnto_eq_append tail (.cons edge.reverse (.nil start))
      rw [reversed, included.resplit_append _ _ edge.vertices.2 first]
      change ChainComparison edges vertices
        ((included.resplit tail.reverse edge.vertices.2).append
          ((Geometry.Grid.Walks.splitSegment grid (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse
            edge.segment) (included.vertex edge.vertices.2) (included.vertex first)).append (.nil start)))
        (((Geometry.Grid.Walks.splitSegment grid edge.segment (included.vertex first) (included.vertex
          edge.vertices.2)).append
          (included.resplit tail last)).reverse)
      rw [Walk.append_nil,
        Walk.reverse_append]
      exact (ih edge.vertices.2 last).append (Geometry.Grid.Extension.split_reverse edges vertices reference
        edge.segment
        (included.vertex first) (included.vertex edge.vertices.2))

/-- Resplitting a stem-based loop compares to basing the resplit loop at the resplit original stem. -/
theorem resplit_based {start finish : Canonical} (stem : Walk original start finish)
    (loop : Walk original finish finish) (first : FromStates.ContainsVertex
      original start) (last : FromStates.ContainsVertex original finish) :
    ChainComparison edges vertices
      (included.resplit (stem.based loop) first)
      ((included.resplit stem last).based (included.resplit loop last)) := by
  change ChainComparison edges vertices (included.resplit (stem.append
    (loop.append stem.reverse)) first) _
  rw [included.resplit_append _ _ last first, included.resplit_append _ _ last first]
  exact (ChainComparison.refl _).append
    ((ChainComparison.refl _).append (included.resplit_reverse edges
      vertices reference stem first last))

end CoordinateInclusion
end Purelib.Polynomial.Geometry.Grid.Extension
