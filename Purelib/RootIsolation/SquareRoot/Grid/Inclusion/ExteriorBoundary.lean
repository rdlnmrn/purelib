module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.AxisSpines
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-! The resplit original ambient boundary and the enlarged grid's literal
ambient boundary agree on each lifted sheet, up to certified retracing. -/

namespace Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {original grid :
  ClearGrid polynomial ambient}
  (included : Geometry.Grid.Extension.CoordinateInclusion original grid)

/-- Resplitting a retained horizontal lookup walk gives the finer-grid walk on the same oriented axis. -/
private theorem horizontal_lookup {first last y : Fraction.Rational}
    (oldAxis : Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk original.xIntervals first last)
    (oldLine : Purelib.Polynomial.Geometry.Grid.AxisWalks.Lookup (key :=
      Geometry.Grid.ClearGrid.HorizontalLine.coordinate) original.horizontal y)
    (lastMember : last ∈ original.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (lineMember : y ∈ original.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (axis : Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals first last)
    (line : Purelib.Polynomial.Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      grid.horizontal y) :
    included.resplit (Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal oldAxis oldLine)
      ⟨lastMember, lineMember⟩ =
      Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal axis line := by
  rcases oldLine with ⟨entry, member, rfl⟩
  exact included.resplit_horizontalIncreasing entry member oldAxis lastMember axis line

/-- Resplitting a retained vertical lookup walk gives the finer-grid walk on the same oriented axis. -/
private theorem vertical_lookup {first last x : Fraction.Rational}
    (oldAxis : Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk original.yIntervals first last)
    (oldLine : Purelib.Polynomial.Geometry.Grid.AxisWalks.Lookup (key :=
      Geometry.Grid.ClearGrid.VerticalLine.coordinate) original.vertical x)
    (lineMember : x ∈ original.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (lastMember : last ∈ original.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (axis : Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals first last)
    (line : Purelib.Polynomial.Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate)
      grid.vertical x) :
    included.resplit (Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical oldLine oldAxis)
      ⟨lineMember, lastMember⟩ =
      Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line axis := by
  rcases oldLine with ⟨entry, member, rfl⟩
  exact included.resplit_verticalIncreasing entry member oldAxis lastMember axis line

/-- Resplitting an original full-frame horizontal axis gives the retained finer frame's axis. -/
private theorem horizontal_axes (oldFrame : FramedClearGrid.AmbientFrame original) (frame :
  FramedClearGrid.AmbientFrame grid)
    (y : Fraction.Rational) (oldMember : y ∈ original.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (member : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    included.resplit (oldFrame.axes.horizontal y oldMember) ⟨oldFrame.xUpper, oldMember⟩ = frame.axes.horizontal y
      member :=
  Geometry.Grid.Extension.CoordinateInclusion.horizontal_lookup included oldFrame.axes.x (Geometry.Grid.AxisWalks.lookup
    y original.horizontal oldMember) oldFrame.xUpper oldMember
    frame.axes.x (Geometry.Grid.AxisWalks.lookup y grid.horizontal member)

/-- Resplitting an original full-frame vertical axis gives the retained finer frame's axis. -/
private theorem vertical_axes (oldFrame : FramedClearGrid.AmbientFrame original) (frame :
  FramedClearGrid.AmbientFrame grid)
    (x : Fraction.Rational) (oldMember : x ∈ original.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (member : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate) :
    included.resplit (oldFrame.axes.vertical x oldMember) ⟨oldMember, oldFrame.yUpper⟩ = frame.axes.vertical x member :=
  Geometry.Grid.Extension.CoordinateInclusion.vertical_lookup included oldFrame.axes.y (Geometry.Grid.AxisWalks.lookup x
    original.vertical oldMember) oldMember oldFrame.yUpper
    frame.axes.y (Geometry.Grid.AxisWalks.lookup x grid.vertical member)

/-- Preserve the individual sheet and full ordered edge polygon, not just
the sum of two exterior integrals. Root frames are never identified. -/
theorem exterior_comparison (oldFrame : FramedClearGrid.AmbientFrame original) (frame :
  FramedClearGrid.AmbientFrame grid)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
      (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit oldFrame.boundary
      ⟨oldFrame.xLower, oldFrame.yLower⟩) frame.boundary := by
  have bottom := Geometry.Grid.Extension.CoordinateInclusion.horizontal_axes included oldFrame frame ambient.yLower
    oldFrame.yLower frame.yLower
  have right := Geometry.Grid.Extension.CoordinateInclusion.vertical_axes included oldFrame frame ambient.xUpper
    oldFrame.xUpper frame.xUpper
  have top := Geometry.Grid.Extension.CoordinateInclusion.horizontal_axes included oldFrame frame ambient.yUpper
    oldFrame.yUpper frame.yUpper
  have left := Geometry.Grid.Extension.CoordinateInclusion.vertical_axes included oldFrame frame ambient.xLower
    oldFrame.xLower frame.xLower
  have topReverse := (included.resplit_reverse edges vertices reference (oldFrame.axes.horizontal ambient.yUpper
    oldFrame.yUpper)
    ⟨oldFrame.xLower, oldFrame.yUpper⟩ ⟨oldFrame.xUpper, oldFrame.yUpper⟩).trans
    (AxisChainCoherence.RootEdgeBank.ChainComparison.reverse reference
      (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq top))
  have leftReverse := (included.resplit_reverse edges vertices reference (oldFrame.axes.vertical ambient.xLower
    oldFrame.xLower)
    ⟨oldFrame.xLower, oldFrame.yLower⟩ ⟨oldFrame.xLower, oldFrame.yUpper⟩).trans
    (AxisChainCoherence.RootEdgeBank.ChainComparison.reverse reference
      (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq left))
  unfold FramedClearGrid.AmbientFrame.boundary
  rw [included.resplit_append _ _ ⟨oldFrame.xUpper, oldFrame.yLower⟩ ⟨oldFrame.xLower, oldFrame.yLower⟩,
    included.resplit_append _ _ ⟨oldFrame.xUpper, oldFrame.yUpper⟩ ⟨oldFrame.xLower, oldFrame.yLower⟩,
    included.resplit_append _ _ ⟨oldFrame.xLower, oldFrame.yUpper⟩ ⟨oldFrame.xLower, oldFrame.yLower⟩]
  exact (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq bottom).append
    ((SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq right).append (topReverse.append
    leftReverse))

end Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion
