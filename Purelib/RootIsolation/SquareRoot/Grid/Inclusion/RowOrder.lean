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
  {original grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} (included :
    Geometry.Grid.Extension.CoordinateInclusion original grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
  (band : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial := polynomial)
    (ambient := ambient)))
  (bandMember : band ∈ original.yIntervals)

namespace Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

/-- The resplit cell boundary compares to the same rectangle with the supplied original left edge. -/
private theorem cell_with_left
    (interval : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (adjacent : interval ∈ original.xIntervals)
    (left : Geometry.Grid.Walks.Edge original (Gaussian.Components.Basic.point interval.lower.coordinate
      band.lower.coordinate) (Gaussian.Components.Basic.point interval.lower.coordinate band.upper.coordinate)) :
    let cell := Geometry.Grid.ClearGrid.Cell.mk interval band
    let onGrid := Geometry.Grid.EdgeSides.EdgeCell.cell_member (grid := original) (cell :=
      Geometry.Grid.ClearGrid.Cell.mk interval band) adjacent bandMember
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell onGrid) left.vertices.1)
      (included.resplit (Geometry.Grid.Walks.Walk.rectangle (.cons (cell.bottomSide onGrid) (.nil _)) (.cons
        (cell.rightSide onGrid) (.nil _))
        (.cons (.horizontal interval adjacent band.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
          original.horizontal_ordered bandMember).2) (.nil _))
        (.cons left (.nil _))) left.vertices.1) := by
  intro cell onGrid
  let initialWalk : Geometry.Grid.Walks.Walk original cell.box.anchor (Gaussian.Components.Basic.point
    interval.lower.coordinate band.upper.coordinate) :=
    .cons (cell.bottomSide onGrid) (.cons (cell.rightSide onGrid) (.cons (cell.topSide onGrid) (.nil _)))
  change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
    (included.resplit (initialWalk.append (.cons (cell.leftSide onGrid) (.nil _))) left.vertices.1)
    (included.resplit (initialWalk.append (.cons (.reverse left) (.nil _))) left.vertices.1)
  erw [included.resplit_append _ _ left.vertices.2 left.vertices.1,
    included.resplit_append _ _ left.vertices.2 left.vertices.1]
  exact (SquareRoot.Grid.RootEdgeBank.ChainComparison.refl _).append
    (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq (included.resplit_edge (cell.leftSide
      onGrid) (.reverse left)))

end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

include reference

namespace Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

/-- The resplit row-circuit product compares to the retained row boundary in its original right-before-left order.

The recursive comparison preserves the actual connector words and cancels shared sides on their arriving sheets. -/
theorem resplit_comparison :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk original.xIntervals start
      finish) →
    (left : Geometry.Grid.Walks.Edge original (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point start band.upper.coordinate)) →
    (right : Geometry.Grid.Walks.Edge original (Gaussian.Components.Basic.point finish band.lower.coordinate)
      (Gaussian.Components.Basic.point finish band.upper.coordinate)) →
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band bandMember walk).product left.vertices.1)
      (included.resplit (Geometry.Grid.RowCircuitOrder.RowCircuits.boundary band bandMember walk left right)
        left.vertices.1)
  | _, _, .nil _, left, right => by
      have rectangle := included.resplit_rectangle edges vertices reference (.nil _) (.cons right (.nil _))
        (.nil _) (.cons left (.nil _)) left.vertices.1 right.vertices.1 left.vertices.2 right.vertices.2
      change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
        (included.resplit (Geometry.Grid.RowCircuitOrder.RowCircuits.boundary band bandMember (.nil _) left right)
          left.vertices.1)
        ((included.resplit (.cons right (.nil _)) right.vertices.2).append
          (included.resplit (.cons left (.nil _)) left.vertices.2).reverse) at rectangle
      rw [included.resplit_edge right left] at rectangle
      exact (SquareRoot.Grid.RootEdgeBank.ChainComparison.retrace reference (included.resplit
        (.cons left (.nil _)) left.vertices.2)).symm.trans rectangle.symm
  | _, _, .cons interval adjacent tail, left, right => by
      let cell := Geometry.Grid.ClearGrid.Cell.mk interval band
      let onGrid := Geometry.Grid.EdgeSides.EdgeCell.cell_member (grid := original) (cell :=
        Geometry.Grid.ClearGrid.Cell.mk interval band) adjacent bandMember
      let stem : Geometry.Grid.Walks.Walk original cell.box.anchor (Gaussian.Components.Basic.point
        interval.upper.coordinate band.lower.coordinate) :=
        .cons (cell.bottomSide onGrid) (.nil _)
      let upper : Geometry.Grid.Walks.Walk original (Gaussian.Components.Basic.point interval.lower.coordinate
        band.upper.coordinate) (Gaussian.Components.Basic.point interval.upper.coordinate band.upper.coordinate) :=
        .cons (.horizontal interval adjacent band.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
          original.horizontal_ordered bandMember).2) (.nil _)
      have tailComparison := Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits.resplit_comparison tail
        (cell.rightSide onGrid) right
      have based := (Geometry.Grid.RowCircuitOrder.CellCircuits.resplit_based_product included edges vertices reference
        stem (Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band bandMember tail)
          left.vertices.1 (cell.rightSide onGrid).vertices.1).trans
        ((tailComparison.based (included.resplit stem (cell.rightSide onGrid).vertices.1)).trans
          (included.resplit_based edges vertices reference stem (Geometry.Grid.RowCircuitOrder.RowCircuits.boundary band
            bandMember tail (cell.rightSide onGrid) right)
            left.vertices.1 (cell.rightSide onGrid).vertices.1).symm)
      have head := Geometry.Grid.RowCircuitOrder.RowCircuits.cell_with_left included edges vertices band bandMember
        interval adjacent left
      have joined := based.append head
      have sewn := included.resplit_horizontal_sewing edges vertices reference stem
        (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band bandMember tail)
        (.cons right (.nil _)) (Geometry.Grid.RowCircuitOrder.RowCircuits.top band bandMember tail) upper (.cons left
          (.nil _)) (.cons (cell.rightSide onGrid) (.nil _))
        left.vertices.1 (cell.rightSide onGrid).vertices.1 right.vertices.1 left.vertices.2
        (cell.rightSide onGrid).vertices.2 right.vertices.2
      erw [included.resplit_append _ _ left.vertices.1 left.vertices.1] at sewn
      apply (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans (joined.trans sewn)
      erw [← included.resplit_append _ _ left.vertices.1 left.vertices.1]
      apply congrArg (fun walk => included.resplit walk left.vertices.1)
      simp only [Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk, Geometry.Grid.RowCircuitOrder.CellCircuits.product,
        Geometry.Grid.Walks.Walk.based, Geometry.Grid.Walks.Walk.append, Geometry.Grid.Walks.Walk.reverse,
        Geometry.Grid.Walks.Walk.reverseOnto, -eq_self, -iff_self]
      exact congrArg (fun rest => ((Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band bandMember tail).based
        stem).product.append rest)
        (Geometry.Grid.Walks.Walk.append_nil (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell
          onGrid))

end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

end
