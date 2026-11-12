module
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CircuitSewing
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Data.Gaussian.Components

public section

/-! The original right-to-left cell order still sews to its full strip
boundary after subdivision, without replacing cells by the new mesh order. -/

section
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib
open Purelib.RootIsolation

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}
  {original grid : Geometry.Grid.ClearGrid polynomial ambient} (included :
    Geometry.Grid.Extension.CoordinateInclusion original grid)
  {frames : SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : LiftedVertices.VertexBank grid)
  (reference : ∀ point, Geometry.Grid.FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
  (band : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial := polynomial)
    (ambient := ambient)))
  (bandMember : band ∈ original.yIntervals)

namespace Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

/-- The resplit cell boundary compares to the same rectangle with the supplied original left edge. -/
private theorem cell_with_left
    (interval : ClearGrid.Interval (ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (adjacent : interval ∈ original.xIntervals)
    (left : Walks.Edge original (Basic.point interval.lower.coordinate
      band.lower.coordinate) (Basic.point interval.lower.coordinate band.upper.coordinate)) :
    let cell := ClearGrid.Cell.mk interval band
    let onGrid := EdgeSides.EdgeCell.cell_member (grid := original) (cell :=
      ClearGrid.Cell.mk interval band) adjacent bandMember
    RootEdgeBank.ChainComparison edges vertices (included.resplit
      (CellBoundary.Cell.boundaryWalk cell onGrid) left.vertices.1)
      (included.resplit (Walks.Walk.rectangle (.cons (cell.bottomSide onGrid) (.nil _)) (.cons
        (cell.rightSide onGrid) (.nil _))
        (.cons (.horizontal interval adjacent band.upper (ClearGrid.Interval.endpoints_mem _
          original.horizontal_ordered bandMember).2) (.nil _))
        (.cons left (.nil _))) left.vertices.1) := by
  intro cell onGrid
  let initialWalk : Walks.Walk original cell.box.anchor (Basic.point
    interval.lower.coordinate band.upper.coordinate) :=
    .cons (cell.bottomSide onGrid) (.cons (cell.rightSide onGrid) (.cons (cell.topSide onGrid) (.nil _)))
  change RootEdgeBank.ChainComparison edges vertices
    (included.resplit (initialWalk.append (.cons (cell.leftSide onGrid) (.nil _))) left.vertices.1)
    (included.resplit (initialWalk.append (.cons (.reverse left) (.nil _))) left.vertices.1)
  erw [included.resplit_append _ _ left.vertices.2 left.vertices.1,
    included.resplit_append _ _ left.vertices.2 left.vertices.1]
  exact (RootEdgeBank.ChainComparison.refl _).append
    (RootEdgeBank.ChainComparison.of_eq (included.resplit_edge (cell.leftSide
      onGrid) (.reverse left)))

end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

include reference

namespace Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

/-- The resplit row-circuit product compares to the retained row boundary in its original right-before-left order.

The recursive comparison preserves the actual connector words and cancels shared sides on their arriving sheets. -/
theorem resplit_comparison :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk original.xIntervals start
      finish) →
    (left : Walks.Edge original (Basic.point start band.lower.coordinate)
      (Basic.point start band.upper.coordinate)) →
    (right : Walks.Edge original (Basic.point finish band.lower.coordinate)
      (Basic.point finish band.upper.coordinate)) →
    RootEdgeBank.ChainComparison edges vertices (included.resplit
      (ofWalk band bandMember walk).product left.vertices.1)
      (included.resplit (boundary band bandMember walk left right)
        left.vertices.1)
  | _, _, .nil _, left, right => by
      have rectangle := included.resplit_rectangle edges vertices reference (.nil _) (.cons right (.nil _))
        (.nil _) (.cons left (.nil _)) left.vertices.1 right.vertices.1 left.vertices.2 right.vertices.2
      change RootEdgeBank.ChainComparison edges vertices
        (included.resplit (boundary band bandMember (.nil _) left right)
          left.vertices.1)
        ((included.resplit (.cons right (.nil _)) right.vertices.2).append
          (included.resplit (.cons left (.nil _)) left.vertices.2).reverse) at rectangle
      rw [included.resplit_edge right left] at rectangle
      exact (RootEdgeBank.ChainComparison.retrace reference (included.resplit
        (.cons left (.nil _)) left.vertices.2)).symm.trans rectangle.symm
  | _, _, .cons interval adjacent tail, left, right => by
      let cell := ClearGrid.Cell.mk interval band
      let onGrid := EdgeSides.EdgeCell.cell_member (grid := original) (cell :=
        ClearGrid.Cell.mk interval band) adjacent bandMember
      let stem : Walks.Walk original cell.box.anchor (Basic.point
        interval.upper.coordinate band.lower.coordinate) :=
        .cons (cell.bottomSide onGrid) (.nil _)
      let upper : Walks.Walk original (Basic.point interval.lower.coordinate
        band.upper.coordinate) (Basic.point interval.upper.coordinate band.upper.coordinate) :=
        .cons (.horizontal interval adjacent band.upper (ClearGrid.Interval.endpoints_mem _
          original.horizontal_ordered bandMember).2) (.nil _)
      have tailComparison := RowCircuits.resplit_comparison tail
        (cell.rightSide onGrid) right
      have based := (CellCircuits.resplit_based_product included edges vertices reference
        stem (ofWalk band bandMember tail)
          left.vertices.1 (cell.rightSide onGrid).vertices.1).trans
        ((tailComparison.based (included.resplit stem (cell.rightSide onGrid).vertices.1)).trans
          (included.resplit_based edges vertices reference stem (boundary band
            bandMember tail (cell.rightSide onGrid) right)
            left.vertices.1 (cell.rightSide onGrid).vertices.1).symm)
      have head := cell_with_left included edges vertices band bandMember
        interval adjacent left
      have joined := based.append head
      have sewn := included.resplit_horizontal_sewing edges vertices reference stem
        (bottom band bandMember tail)
        (.cons right (.nil _)) (top band bandMember tail) upper (.cons left
          (.nil _)) (.cons (cell.rightSide onGrid) (.nil _))
        left.vertices.1 (cell.rightSide onGrid).vertices.1 right.vertices.1 left.vertices.2
        (cell.rightSide onGrid).vertices.2 right.vertices.2
      erw [included.resplit_append _ _ left.vertices.1 left.vertices.1] at sewn
      apply (RootEdgeBank.ChainComparison.of_eq ?_).trans (joined.trans sewn)
      erw [← included.resplit_append _ _ left.vertices.1 left.vertices.1]
      apply congrArg (fun walk => included.resplit walk left.vertices.1)
      simp only [ofWalk, CellCircuits.product,
        Walks.Walk.based, Walks.Walk.append, Walks.Walk.reverse,
        Walks.Walk.reverseOnto, -eq_self, -iff_self]
      exact congrArg (fun rest => ((ofWalk band bandMember tail).based
        stem).product.append rest)
        (Walks.Walk.append_nil (CellBoundary.Cell.boundaryWalk cell
          onGrid))

end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

end
