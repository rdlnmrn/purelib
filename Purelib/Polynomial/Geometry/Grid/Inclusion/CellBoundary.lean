module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.Axis.Full
import Purelib.Polynomial.Geometry.Grid.WindowAxes
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-! The subdivided original four-sided cell boundary has the same finite
edge sums as the retained window, for arbitrary oriented edge readings. -/

namespace Purelib.Polynomial.Geometry.Grid.Inclusion.CellBoundary

open Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient} {box : Box}

/-- A forward horizontal split reads as the sum over the window's exact cached horizontal intervals. -/
private theorem horizontal_forward (window : WindowBoundary.Window grid box) (values :
  CellBoundary.EdgeValues) (y : Fraction.Rational)
    (lower : box.xLower ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (upper : box.xUpper ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (line : y ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) :
    values.walk (Walks.horizontalWalk grid box.xLower box.xUpper y lower upper line) =
      CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate y) window.x.edges := by
  rw [Walks.horizontalWalk, Axis.Full.EdgeValues.walk_castEndpoints,
    AxisWalks.walk, dif_pos box.x_valid]
  change values.walk (Walks.Walk.horizontalIncreasing _ _ _) = _
  rw [Axis.Full.EdgeValues.walk_horizontalIncreasing]
  have equal := WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _)
    (AxisWalks.increasing box.xLower box.xUpper grid.vertical grid.vertical_ordered lower upper
      box.x_valid)
  rw [← WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _) window.x] at equal
  erw [equal]
  exact CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (values.horizontal interval.lower.coordinate interval.upper.coordinate) (AxisWalks.lookup y
      grid.horizontal line).coordinate_eq)

/-- A forward vertical split reads as the sum over the window's exact cached vertical intervals. -/
private theorem vertical_forward (window : WindowBoundary.Window grid box) (values :
  CellBoundary.EdgeValues) (x : Fraction.Rational)
    (line : x ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (lower : box.yLower ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate)
    (upper : box.yUpper ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) :
    values.walk (Walks.verticalWalk grid x box.yLower box.yUpper line lower upper) =
      CellBoundary.sumValues (fun interval => values.vertical x interval.lower.coordinate
        interval.upper.coordinate) window.y.edges := by
  rw [Walks.verticalWalk, Axis.Full.EdgeValues.walk_castEndpoints,
    AxisWalks.walk, dif_pos box.y_valid]
  change values.walk (Walks.Walk.verticalIncreasing _ _ _) = _
  rw [Axis.Full.EdgeValues.walk_verticalIncreasing]
  have equal := WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _)
    (AxisWalks.increasing box.yLower box.yUpper grid.horizontal grid.horizontal_ordered lower upper
      box.y_valid)
  rw [← WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _) window.y] at equal
  erw [equal]
  exact CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (fun coordinate => values.vertical coordinate interval.lower.coordinate interval.upper.coordinate)
    (AxisWalks.lookup x grid.vertical line).coordinate_eq)

/-- A backward horizontal split reads as the negative sum over the window's cached horizontal intervals. -/
private theorem horizontal_backward (window : WindowBoundary.Window grid box) (values :
  CellBoundary.EdgeValues) (y : Fraction.Rational)
    (lower : box.xLower ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (upper : box.xUpper ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (line : y ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) (strict : box.xLower <
      box.xUpper) :
    values.walk (Walks.horizontalWalk grid box.xUpper box.xLower y upper lower line) =
      -CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate y) window.x.edges := by
  rw [Walks.horizontalWalk, Axis.Full.EdgeValues.walk_castEndpoints,
    AxisWalks.walk, dif_neg (not_le_of_gt strict)]
  change values.walk (Walks.Walk.horizontalIncreasing _ _ _).reverse = _
  rw [CellBoundary.EdgeValues.walk_reverse,
    Axis.Full.EdgeValues.walk_horizontalIncreasing]
  have equal := WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _)
    (AxisWalks.increasing box.xLower box.xUpper grid.vertical grid.vertical_ordered lower upper
      (le_of_not_ge (not_le_of_gt strict)))
  rw [← WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _) window.x] at equal
  erw [equal]
  apply congrArg Neg.neg
  exact CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (values.horizontal interval.lower.coordinate interval.upper.coordinate) (AxisWalks.lookup y
      grid.horizontal line).coordinate_eq)

/-- A backward vertical split reads as the negative sum over the window's cached vertical intervals. -/
private theorem vertical_backward (window : WindowBoundary.Window grid box) (values :
  CellBoundary.EdgeValues) (x : Fraction.Rational)
    (line : x ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (lower : box.yLower ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate)
    (upper : box.yUpper ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) (strict : box.yLower <
      box.yUpper) :
    values.walk (Walks.verticalWalk grid x box.yUpper box.yLower line upper lower) =
      -CellBoundary.sumValues (fun interval => values.vertical x interval.lower.coordinate
        interval.upper.coordinate) window.y.edges := by
  rw [Walks.verticalWalk, Axis.Full.EdgeValues.walk_castEndpoints,
    AxisWalks.walk, dif_neg (not_le_of_gt strict)]
  change values.walk (Walks.Walk.verticalIncreasing _ _ _).reverse = _
  rw [CellBoundary.EdgeValues.walk_reverse,
    Axis.Full.EdgeValues.walk_verticalIncreasing]
  have equal := WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _)
    (AxisWalks.increasing box.yLower box.yUpper grid.horizontal grid.horizontal_ordered lower upper
      (le_of_not_ge (not_le_of_gt strict)))
  rw [← WindowAxes.IncreasingWalk.edges_eq_filter
    (ClearGrid.Interval.adjacent_pairwise _ _) window.y] at equal
  erw [equal]
  apply congrArg Neg.neg
  exact CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (fun coordinate => values.vertical coordinate interval.lower.coordinate interval.upper.coordinate)
    (AxisWalks.lookup x grid.vertical line).coordinate_eq)

/-- Resplitting an original cell boundary preserves the retained window's oriented edge reading.

The equality holds for arbitrary edge values and uses the original coordinate inclusion and cell membership. -/
theorem resplit_cell_value {original : ClearGrid polynomial ambient}
    (included : Extension.CoordinateInclusion original grid) (cell : ClearGrid.Cell
      polynomial ambient) (member : cell ∈ original.cells)
    (window : WindowBoundary.Window grid cell.box) (values : CellBoundary.EdgeValues) :
    values.walk (included.resplit
      (CellBoundary.Cell.boundaryWalk cell member)
      (ClearGrid.Cell.anchor_mem cell member)) =
      values.walk window.boundary := open Purelib in by
  simp only [Extension.CoordinateInclusion.resplit, CellBoundary.Cell.boundaryWalk,
    Walks.Walk.path,
    Walks.splitPath, Walks.Edge.segment,
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse,
    Walks.splitSegment, values.walk_append, CellBoundary.EdgeValues.walk]
  erw [horizontal_forward window values _ _ _ _,
    vertical_forward window values _ _ _ _,
    horizontal_backward window values _ _ _ _ cell.horizontal.ordered,
    vertical_backward window values _ _ _ _ cell.vertical.ordered,
    window.boundary_value]
  dsimp only [WindowBoundary.Window.perimeter]
  rw [CellBoundary.sumValues_sub,
    CellBoundary.sumValues_sub]
  dsimp only [ClearGrid.Cell.box]
  ring1

end Purelib.Polynomial.Geometry.Grid.Inclusion.CellBoundary
