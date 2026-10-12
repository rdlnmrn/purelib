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

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient} {box : Box}

/-- A forward horizontal split reads as the sum over the window's exact cached horizontal intervals. -/
private theorem horizontal_forward (window : WindowBoundary.Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) (y : Fraction.Rational)
    (lower : box.xLower ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (upper : box.xUpper ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (line : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    values.walk (Geometry.Grid.Walks.horizontalWalk grid box.xLower box.xUpper y lower upper line) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate y) window.x.edges := by
  rw [Geometry.Grid.Walks.horizontalWalk, Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.AxisWalks.walk, dif_pos box.x_valid]
  change values.walk (Geometry.Grid.Walks.Walk.horizontalIncreasing _ _ _) = _
  rw [Geometry.Grid.Axis.Full.EdgeValues.walk_horizontalIncreasing]
  have equal := Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _)
    (Geometry.Grid.AxisWalks.increasing box.xLower box.xUpper grid.vertical grid.vertical_ordered lower upper
      box.x_valid)
  rw [← Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _) window.x] at equal
  erw [equal]
  exact Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (values.horizontal interval.lower.coordinate interval.upper.coordinate) (Geometry.Grid.AxisWalks.lookup y
      grid.horizontal line).coordinate_eq)

/-- A forward vertical split reads as the sum over the window's exact cached vertical intervals. -/
private theorem vertical_forward (window : WindowBoundary.Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) (x : Fraction.Rational)
    (line : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (lower : box.yLower ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (upper : box.yUpper ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    values.walk (Geometry.Grid.Walks.verticalWalk grid x box.yLower box.yUpper line lower upper) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.vertical x interval.lower.coordinate
        interval.upper.coordinate) window.y.edges := by
  rw [Geometry.Grid.Walks.verticalWalk, Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.AxisWalks.walk, dif_pos box.y_valid]
  change values.walk (Geometry.Grid.Walks.Walk.verticalIncreasing _ _ _) = _
  rw [Geometry.Grid.Axis.Full.EdgeValues.walk_verticalIncreasing]
  have equal := Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _)
    (Geometry.Grid.AxisWalks.increasing box.yLower box.yUpper grid.horizontal grid.horizontal_ordered lower upper
      box.y_valid)
  rw [← Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _) window.y] at equal
  erw [equal]
  exact Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (fun coordinate => values.vertical coordinate interval.lower.coordinate interval.upper.coordinate)
    (Geometry.Grid.AxisWalks.lookup x grid.vertical line).coordinate_eq)

/-- A backward horizontal split reads as the negative sum over the window's cached horizontal intervals. -/
private theorem horizontal_backward (window : WindowBoundary.Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) (y : Fraction.Rational)
    (lower : box.xLower ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (upper : box.xUpper ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (line : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) (strict : box.xLower <
      box.xUpper) :
    values.walk (Geometry.Grid.Walks.horizontalWalk grid box.xUpper box.xLower y upper lower line) =
      -Geometry.Grid.CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate y) window.x.edges := by
  rw [Geometry.Grid.Walks.horizontalWalk, Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.AxisWalks.walk, dif_neg (not_le_of_gt strict)]
  change values.walk (Geometry.Grid.Walks.Walk.horizontalIncreasing _ _ _).reverse = _
  rw [Geometry.Grid.CellBoundary.EdgeValues.walk_reverse,
    Geometry.Grid.Axis.Full.EdgeValues.walk_horizontalIncreasing]
  have equal := Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _)
    (Geometry.Grid.AxisWalks.increasing box.xLower box.xUpper grid.vertical grid.vertical_ordered lower upper
      (le_of_not_ge (not_le_of_gt strict)))
  rw [← Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _) window.x] at equal
  erw [equal]
  apply congrArg Neg.neg
  exact Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (values.horizontal interval.lower.coordinate interval.upper.coordinate) (Geometry.Grid.AxisWalks.lookup y
      grid.horizontal line).coordinate_eq)

/-- A backward vertical split reads as the negative sum over the window's cached vertical intervals. -/
private theorem vertical_backward (window : WindowBoundary.Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) (x : Fraction.Rational)
    (line : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (lower : box.yLower ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (upper : box.yUpper ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) (strict : box.yLower <
      box.yUpper) :
    values.walk (Geometry.Grid.Walks.verticalWalk grid x box.yUpper box.yLower line upper lower) =
      -Geometry.Grid.CellBoundary.sumValues (fun interval => values.vertical x interval.lower.coordinate
        interval.upper.coordinate) window.y.edges := by
  rw [Geometry.Grid.Walks.verticalWalk, Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.AxisWalks.walk, dif_neg (not_le_of_gt strict)]
  change values.walk (Geometry.Grid.Walks.Walk.verticalIncreasing _ _ _).reverse = _
  rw [Geometry.Grid.CellBoundary.EdgeValues.walk_reverse,
    Geometry.Grid.Axis.Full.EdgeValues.walk_verticalIncreasing]
  have equal := Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _)
    (Geometry.Grid.AxisWalks.increasing box.yLower box.yUpper grid.horizontal grid.horizontal_ordered lower upper
      (le_of_not_ge (not_le_of_gt strict)))
  rw [← Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _) window.y] at equal
  erw [equal]
  apply congrArg Neg.neg
  exact Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun interval _ => congrArg
    (fun coordinate => values.vertical coordinate interval.lower.coordinate interval.upper.coordinate)
    (Geometry.Grid.AxisWalks.lookup x grid.vertical line).coordinate_eq)

/-- Resplitting an original cell boundary preserves the retained window's oriented edge reading.

The equality holds for arbitrary edge values and uses the original coordinate inclusion and cell membership. -/
theorem resplit_cell_value {original : ClearGrid polynomial ambient}
    (included : Geometry.Grid.Extension.CoordinateInclusion original grid) (cell : Geometry.Grid.ClearGrid.Cell
      polynomial ambient) (member : cell ∈ original.cells)
    (window : WindowBoundary.Window grid cell.box) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    values.walk (included.resplit
      (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell member)
      (Geometry.Grid.ClearGrid.Cell.anchor_mem cell member)) =
      values.walk window.boundary := open Purelib in by
  simp only [Geometry.Grid.Extension.CoordinateInclusion.resplit, Geometry.Grid.CellBoundary.Cell.boundaryWalk,
    Geometry.Grid.Walks.Walk.path,
    Geometry.Grid.Walks.splitPath, Geometry.Grid.Walks.Edge.segment,
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse,
    Geometry.Grid.Walks.splitSegment, values.walk_append, Geometry.Grid.CellBoundary.EdgeValues.walk]
  erw [Geometry.Grid.Inclusion.CellBoundary.horizontal_forward window values _ _ _ _,
    Geometry.Grid.Inclusion.CellBoundary.vertical_forward window values _ _ _ _,
    Geometry.Grid.Inclusion.CellBoundary.horizontal_backward window values _ _ _ _ cell.horizontal.ordered,
    Geometry.Grid.Inclusion.CellBoundary.vertical_backward window values _ _ _ _ cell.vertical.ordered,
    window.boundary_value]
  dsimp only [WindowBoundary.Window.perimeter]
  rw [Geometry.Grid.CellBoundary.sumValues_sub,
    Geometry.Grid.CellBoundary.sumValues_sub]
  dsimp only [Geometry.Grid.ClearGrid.Cell.box]
  ring1

end Purelib.Polynomial.Geometry.Grid.Inclusion.CellBoundary
