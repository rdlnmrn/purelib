module
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

public section

/-!
# Exact observed area under rectangular subdivision

Clamped coordinate increments measure the part of a rectangle lying in an
observation box. Their finite telescoping identity preserves that area under
any retained rectangular partition. On a classified piece the value is its
whole area or zero, including pieces which share an observation boundary.
-/

namespace Purelib.Geometry.Rectangle.Partition.PreparedRectangleOverlap

open _root_.Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (sumCells sumCells_append)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

/-- Clamp a rational coordinate to two ordered interval endpoints. -/
@[expose] def clamp (lower upper point : Fraction.Rational) : Fraction.Rational :=
  if point ≤ lower then lower else if upper ≤ point then upper else point

/-- A coordinate below the interval clamps to the lower endpoint. -/
private theorem clamp_below {lower upper point : Fraction.Rational} (below : point ≤ lower) :
    clamp lower upper point = lower := by rw
      [clamp, if_pos below]

/-- A coordinate above an ordered interval clamps to the upper endpoint. -/
private theorem clamp_above {lower upper point : Fraction.Rational} (ordered : lower ≤ upper) (above : upper ≤ point) :
    clamp lower upper point = upper := by
  unfold clamp
  split
  · rename_i below
    exact le_antisymm ordered (above.trans below)
  · rfl

/-- A coordinate inside the closed interval is unchanged by clamping. -/
private theorem clamp_inside {lower upper point : Fraction.Rational} (first : lower ≤ point) (last : point ≤ upper) :
    clamp lower upper point = point := by
  unfold clamp
  split
  · rename_i below
    exact le_antisymm first below
  · split
    · rename_i above
      exact le_antisymm above last
    · rfl

/-- Finite overlap area, computed without constructing an intersection box. -/
@[expose] def content (observed piece : Rational.Box) : Fraction.Rational :=
  (clamp observed.xLower observed.xUpper piece.xUpper -
    clamp observed.xLower observed.xUpper piece.xLower) *
    (clamp observed.yLower observed.yUpper piece.yUpper -
      clamp observed.yLower observed.yUpper piece.yLower)

/-- A piece contained in the observation box contributes its full area. -/
theorem content_refines {observed piece : Rational.Box} (inside : piece.Refines observed) :
    content observed piece = Content.boxContent piece := by
  unfold content
  rw [clamp_inside (inside.1.trans piece.x_valid) inside.2.1,
    clamp_inside inside.1 (piece.x_valid.trans inside.2.1),
    clamp_inside (inside.2.2.1.trans piece.y_valid) inside.2.2.2,
    clamp_inside inside.2.2.1 (piece.y_valid.trans inside.2.2.2)]
  rfl

/-- A piece containing the observation box contributes the observation box's full area. -/
theorem content_contains {observed piece : Rational.Box} (inside : observed.Refines piece) :
    content observed piece = Content.boxContent observed := by
  unfold content
  rw [clamp_above observed.x_valid inside.2.1,
    clamp_below inside.1,
    clamp_above observed.y_valid inside.2.2.2,
      clamp_below inside.2.2.1]
  rfl

/-- Interior-separated boxes have zero overlap content. -/
theorem content_separated {observed piece : Rational.Box} (outside : piece.InteriorSeparated observed) :
    content observed piece = 0 := by
  unfold content
  rcases outside with left | right | below | above
  · rw [clamp_below left,
      clamp_below (piece.x_valid.trans left), sub_self, zero_mul]
  · rw [clamp_above observed.x_valid (right.trans piece.x_valid),
      clamp_above observed.x_valid right,
      sub_self, zero_mul]
  · rw [clamp_below below,
      clamp_below (piece.y_valid.trans below), sub_self, mul_zero]
  · rw [clamp_above observed.y_valid (above.trans piece.y_valid),
      clamp_above observed.y_valid above,
      sub_self, mul_zero]

/-- Telescoping uses the actual retained walk, for either scalar cut axes or original grid-line axes. The coordinate
function need not be affine. -/
theorem axis_sum_walk {Alpha : Type} {key : Alpha → Fraction.Rational}
    (value : Fraction.Rational → Fraction.Rational) {intervals : List (ClearGrid.Interval key)} :
    {first last : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk intervals first last) →
      Squares.coordinateSum (walk.edges.map fun interval => value (key interval.upper) - value (key interval.lower)) =
        value last - value first
  | _, _, .nil _ => by change (0 : Fraction.Rational) = _ - _; ring1
  | _, _, .cons interval _ tail => by
      change value (key interval.upper) - value (key interval.lower) + _ = _
      rw [axis_sum_walk value tail]
      ring1

/-- The overlap sum in one column factors into its clamped width and the clamped vertical increments. -/
private theorem row_sum (observed : Rational.Box) (horizontal : PreparedAxisPartitions.Interval)
    (vertical : List PreparedAxisPartitions.Interval) :
    PreparedBoxPartitions.sumCells (content observed)
      (vertical.map (PreparedRectangleCuts.intervalBox horizontal)) =
      (clamp observed.xLower observed.xUpper horizontal.upper -
        clamp observed.xLower observed.xUpper horizontal.lower) *
        Squares.coordinateSum (vertical.map fun interval =>
          clamp observed.yLower observed.yUpper interval.upper -
            clamp observed.yLower observed.yUpper interval.lower)
            := by
  induction vertical with
  | nil => change (0 : Fraction.Rational) = _ * 0; ring1
  | cons first rest ih =>
      change content observed (PreparedRectangleCuts.intervalBox
        horizontal first) + _ = _
      rw [ih]
      dsimp only [-eq_self, -iff_self, content,
        PreparedRectangleCuts.intervalBox]
      change (_ - _) * (_ - _) + (_ - _) * _ = (_ - _) * ((_ - _) + _)
      ring1

/-- The Cartesian overlap sum factors into the product of the two clamped axis sums. -/
private theorem rectangles_sum (observed : Rational.Box) (horizontal vertical : List
  PreparedAxisPartitions.Interval) :
    PreparedBoxPartitions.sumCells (content observed)
      (PreparedRectangleCuts.rectangles horizontal vertical) =
      Squares.coordinateSum (horizontal.map fun interval =>
        clamp observed.xLower observed.xUpper interval.upper -
          clamp observed.xLower observed.xUpper interval.lower) *
      Squares.coordinateSum (vertical.map fun interval =>
        clamp observed.yLower observed.yUpper interval.upper -
          clamp observed.yLower observed.yUpper interval.lower) :=
          by
  induction horizontal with
  | nil => change (0 : Fraction.Rational) = 0 * _; ring1
  | cons first rest ih =>
      change PreparedBoxPartitions.sumCells (content observed)
        ((vertical.map (PreparedRectangleCuts.intervalBox first)) ++ PreparedRectangleCuts.rectangles rest vertical) = _
      rw [PreparedBoxPartitions.sumCells_append, row_sum, ih]
      change (_ - _) * _ + _ * _ = ((_ - _) + _) * _
      ring1

/-- A retained rectangular partition preserves overlap content with the observation box. -/
theorem partition_sum (observed : Rational.Box) {box : Rational.Box} {points : List
  Data.Gaussian.Basic.Canonical}
    (partition : CutPartition box points) :
    PreparedBoxPartitions.sumCells (content observed)
      partition.boxes = content observed box := by
  rw [partition.boxes_eq, rectangles_sum, ←
    partition.x.walk_edges, ← partition.y.walk_edges]
  exact congrArg₂ (fun x y : Fraction.Rational => x * y)
    (axis_sum_walk
      (clamp observed.xLower observed.xUpper) partition.x.walk)
    (axis_sum_walk
      (clamp observed.yLower observed.yUpper) partition.y.walk)

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval Cell VerticalLine HorizontalLine)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Rational.Box}

/-- The original grid's column overlap sum factors through its retained coordinate increments. -/
private theorem grid_row_sum (observed : Rational.Box)
    (horizontal : ClearGrid.Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (vertical : List (ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient)))) :
    Squares.coordinateSum ((vertical.map fun y => (⟨horizontal, y⟩ : ClearGrid.Cell polynomial ambient)).map fun cell =>
      content observed cell.box) =
      (clamp observed.xLower observed.xUpper
        horizontal.upper.coordinate - clamp observed.xLower
        observed.xUpper horizontal.lower.coordinate) *
      Squares.coordinateSum (vertical.map fun interval => clamp
        observed.yLower observed.yUpper interval.upper.coordinate -
        clamp observed.yLower observed.yUpper
          interval.lower.coordinate) := by
  induction vertical with
  | nil => change (0 : Fraction.Rational) = _ * 0; ring1
  | cons first rest ih =>
      change content observed (Cell.box ⟨horizontal, first⟩) + _ =
        _
      rw [ih]
      dsimp only [-eq_self, -iff_self, content, Cell.box]
      change (_ - _) * (_ - _) + (_ - _) * _ = (_ - _) * ((_ - _) + _)
      ring1

/-- The rational coordinate sum is additive over concatenation. -/
private theorem coordinateSum_append (left right : List Fraction.Rational) :
    Squares.coordinateSum (left ++ right) = Squares.coordinateSum left + Squares.coordinateSum right := by
  induction left with
  | nil => change Squares.coordinateSum right = 0 + Squares.coordinateSum right; ring1
  | cons head tail ih =>
    change head + Squares.coordinateSum (tail ++ right) = _; rw [ih]; change _ = (head + Squares.coordinateSum tail) +
      _; ring1

/-- The original grid overlap sum factors into its two retained axis increment sums. -/
private theorem grid_columns_sum (observed : Rational.Box)
    (horizontal : List (ClearGrid.Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient))))
    (vertical : List (ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient)))) :
    Squares.coordinateSum ((horizontal.flatMap fun x => vertical.map fun y => (⟨x, y⟩ : ClearGrid.Cell polynomial
      ambient)).map
      fun cell => content observed cell.box) =
      Squares.coordinateSum (horizontal.map fun interval => clamp
        observed.xLower observed.xUpper interval.upper.coordinate -
        clamp observed.xLower observed.xUpper
          interval.lower.coordinate) *
      Squares.coordinateSum (vertical.map fun interval => clamp
        observed.yLower observed.yUpper interval.upper.coordinate -
        clamp observed.yLower observed.yUpper
          interval.lower.coordinate) := by
  induction horizontal with
  | nil => change (0 : Fraction.Rational) = 0 * _; ring1
  | cons first rest ih =>
      rw [Purelib.Data.List.Flatten.flatMap_cons, Purelib.Data.List.Map.map_append,
        coordinateSum_append,
        grid_row_sum, ih]
      change (_ - _) * _ + _ * _ = ((_ - _) + _) * _
      ring1

/-- The same overlap measure telescopes across the original full grid, before its branch faces are removed. -/
theorem grid_sum (observed : Rational.Box) {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
    (frame : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame grid) :
    Squares.coordinateSum (grid.cells.map fun cell => content
      observed cell.box) = content observed ambient := by
  rw [Grid.cells, grid_columns_sum, ← frame.axes.x_edges, ←
    frame.axes.y_edges]
  exact congrArg₂ (fun x y : Fraction.Rational => x * y)
    (axis_sum_walk
      (clamp observed.xLower observed.xUpper) frame.axes.x)
    (axis_sum_walk
      (clamp observed.yLower observed.yUpper) frame.axes.y)

end Purelib.Geometry.Rectangle.Partition.PreparedRectangleOverlap
