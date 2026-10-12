module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Filter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Polynomial.Geometry.Grid.Axis.Full
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Geometry.Grid.WindowAxes
import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Tactic.Ring

public section

/-!
# Exact cell cancellation inside retained rectangular grid windows

Two cached monotone axes and four cached line lookups supply the literal
subdivided boundary. Filtering the original cell bank retains exactly its
interior cells; their edge readings telescope to that same boundary.
No ambient enlargement or new clearance computation is involved.
-/

namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid.Axis.Full.EdgeValues
open Purelib.Polynomial.Geometry.Grid.WindowAxes.IncreasingWalk

/-- Decide rational box refinement by comparing the four endpoint bounds. -/
instance boxRefinesDecidable (inner outer : Box) : Decidable (inner.Refines outer) := by
  unfold Box.Refines
  infer_instance

/-- Filtering entries preserves their sum with zero assigned to rejected entries.

The supplied decidable predicate retains both branches at every source
occurrence. Scalar addition transports only the unchanged tail equality. -/
theorem sumValues_filter {Alpha : Type} (keep : Alpha → Prop) [decision : DecidablePred keep]
    (value : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
    Geometry.Grid.CellBoundary.sumValues value (entries.filter (fun entry => decide (keep entry))) =
      Geometry.Grid.CellBoundary.sumValues (fun entry => if keep entry then value entry else 0) entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      cases retained : decision head with
      | isTrue kept =>
          have accepted : @decide (keep head) (decision head) = true := by
            rw [retained]
            rfl
          rw [Filter.filter_cons_of_pos (predicate := fun entry => decide (keep entry)) (head := head) (tail := tail)
            accepted]
          change value head + Geometry.Grid.CellBoundary.sumValues value
              (tail.filter (fun entry => decide (keep entry))) =
            (if keep head then value head else 0) + Geometry.Grid.CellBoundary.sumValues
              (fun entry => if keep entry then value entry else 0) tail
          rw [if_pos kept]
          exact congrArg (fun total => value head + total) ih
      | isFalse rejected =>
          have refused : ¬ @decide (keep head) (decision head) = true := by
            rw [retained]
            intro impossible
            nomatch impossible
          rw [Filter.filter_cons_of_neg (predicate := fun entry => decide (keep entry)) (head := head) (tail := tail)
            refused]
          change Geometry.Grid.CellBoundary.sumValues value
              (tail.filter (fun entry => decide (keep entry))) =
            (if keep head then value head else 0) + Geometry.Grid.CellBoundary.sumValues
              (fun entry => if keep entry then value entry else 0) tail
          rw [if_neg rejected, Gaussian.Basic.zero_add]
          exact ih

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

set_option genInjectivity false in
/-- A rectangular window retains checked axis walks, line lookups and selected cells.

The supplied caches use the same grid and physical box. Their cell readback
identifies the exact refinement filter while retaining independent checked
axis and line constructions. -/
structure Window (grid : ClearGrid polynomial ambient) (box : Box) where
  /-- The cached increasing walk between the window's horizontal bounds. -/ x : Geometry.Grid.AxisWalks.IncreasingWalk
    grid.xIntervals box.xLower box.xUpper
  /-- The cached increasing walk between the window's vertical bounds. -/ y : Geometry.Grid.AxisWalks.IncreasingWalk
    grid.yIntervals box.yLower box.yUpper
  /-- The retained clear line at the window's left coordinate. -/ left : Geometry.Grid.AxisWalks.Lookup (key :=
    Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical box.xLower
  /-- The retained clear line at the window's right coordinate. -/ right : Geometry.Grid.AxisWalks.Lookup (key :=
    Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical box.xUpper
  /-- The retained clear line at the window's bottom coordinate. -/ bottom : Geometry.Grid.AxisWalks.Lookup (key :=
    Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal box.yLower
  /-- The retained clear line at the window's top coordinate. -/ top : Geometry.Grid.AxisWalks.Lookup (key :=
    Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal box.yUpper
  /-- The retained original grid cells contained in the window box. -/ cells : List (Geometry.Grid.ClearGrid.Cell
    polynomial ambient)
  /-- The retained cell list is exactly the original grid list filtered by box refinement. -/ cells_eq : cells =
    grid.cells.filter (fun cell => decide (cell.box.Refines box))

constructive_injectivity Window

namespace Window

variable {grid : ClearGrid polynomial ambient} {box : Box}

/-- Build a window from its two cached axis walks and four retained clear lines.

The retained cells are the original grid cells filtered by exact refinement of the window box. -/
@[expose] def build (grid : ClearGrid polynomial ambient) (box : Box)
    (xLower : box.xLower ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (xUpper : box.xUpper ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (yLower : box.yLower ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (yUpper : box.yUpper ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
      Window grid box :=
  ⟨Geometry.Grid.AxisWalks.increasing _ _ grid.vertical grid.vertical_ordered xLower xUpper box.x_valid,
    Geometry.Grid.AxisWalks.increasing _ _ grid.horizontal grid.horizontal_ordered yLower yUpper box.y_valid,
    Geometry.Grid.AxisWalks.lookup _ grid.vertical xLower, Geometry.Grid.AxisWalks.lookup _ grid.vertical xUpper,
    Geometry.Grid.AxisWalks.lookup _ grid.horizontal yLower, Geometry.Grid.AxisWalks.lookup _ grid.horizontal yUpper,
    grid.cells.filter (fun cell => decide (cell.box.Refines box)), rfl⟩

/-- Lift the window's cached horizontal axis walk along a retained clear line. -/
@[expose] def horizontal (window : Window grid box) {y : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point box.xLower y) (Gaussian.Components.Basic.point
      box.xUpper y) :=
  (Geometry.Grid.Walks.Walk.horizontalIncreasing line.entry line.member window.x).castEndpoints
    (congrArg (Gaussian.Components.Basic.point box.xLower) line.coordinate_eq) (congrArg
      (Gaussian.Components.Basic.point box.xUpper) line.coordinate_eq)

/-- Lift the window's cached vertical axis walk along a retained clear line. -/
@[expose] def vertical (window : Window grid box) {x : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point x box.yLower) (Gaussian.Components.Basic.point x
      box.yUpper) :=
  (Geometry.Grid.Walks.Walk.verticalIncreasing line.entry line.member window.y).castEndpoints
    (congrArg (fun x => Gaussian.Components.Basic.point x box.yLower) line.coordinate_eq) (congrArg (fun x =>
      Gaussian.Components.Basic.point x box.yUpper) line.coordinate_eq)

/-- Construct the subdivided positive boundary using the window's retained axis walks.

The top and left sides reverse those exact subdivisions. -/
@[expose] def boundary (window : Window grid box) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point box.xLower box.yLower)
      (Gaussian.Components.Basic.point box.xLower box.yLower) :=
  (window.horizontal window.bottom).append ((window.vertical window.right).append
    ((window.horizontal window.top).reverse.append (window.vertical window.left).reverse))

/-- Sum the oriented boundary readings over the window's cached axis intervals. -/
@[expose] def perimeter (window : Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) : Gaussian.Basic.Canonical :=
  Geometry.Grid.CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
    interval.upper.coordinate box.yLower -
    values.horizontal interval.lower.coordinate interval.upper.coordinate box.yUpper) window.x.edges +
  Geometry.Grid.CellBoundary.sumValues (fun interval => values.vertical box.xUpper interval.lower.coordinate
    interval.upper.coordinate -
    values.vertical box.xLower interval.lower.coordinate interval.upper.coordinate) window.y.edges

/-- The horizontal walk value is the sum of its retained interval readings. -/
theorem horizontal_value (window : Window grid box) {y : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      (values : Geometry.Grid.CellBoundary.EdgeValues) :
    values.walk (window.horizontal line) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate y) window.x.edges := by
  dsimp only [horizontal]
  rw [Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.Axis.Full.EdgeValues.walk_horizontalIncreasing, line.coordinate_eq]

/-- The vertical walk value is the sum of its retained interval readings. -/
theorem vertical_value (window : Window grid box) {x : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x)
      (values : Geometry.Grid.CellBoundary.EdgeValues) :
    values.walk (window.vertical line) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.vertical x interval.lower.coordinate
        interval.upper.coordinate) window.y.edges := by
  dsimp only [vertical]
  rw [Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.Axis.Full.EdgeValues.walk_verticalIncreasing, line.coordinate_eq]

/-- The subdivided boundary reading equals the window perimeter sum. -/
theorem boundary_value (window : Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) :
    values.walk window.boundary = window.perimeter values := by
  dsimp only [boundary, perimeter]
  rw [values.walk_append, values.walk_append, values.walk_append, values.walk_reverse, values.walk_reverse,
    window.horizontal_value, window.horizontal_value, window.vertical_value, window.vertical_value,
    Geometry.Grid.CellBoundary.sumValues_sub, Geometry.Grid.CellBoundary.sumValues_sub]
  ring1

/-- The horizontal window subdivision has the winding of its full oriented edge. -/
theorem horizontal_winding (window : Window grid box) {y : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (window.horizontal line).path =
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial y box.xLower box.xUpper).doubledWinding := by
  dsimp only [horizontal]
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding, Geometry.Grid.Winding.Walk.horizontalIncreasing_winding,
    line.coordinate_eq]

/-- The vertical window subdivision has the winding of its full oriented edge. -/
theorem vertical_winding (window : Window grid box) {x : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (window.vertical line).path =
      (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial x box.yLower box.yUpper).doubledWinding := by
  dsimp only [vertical]
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding, Geometry.Grid.Winding.Walk.verticalIncreasing_winding,
    line.coordinate_eq]

/-- The subdivided window boundary has the raw winding of its box. -/
theorem boundary_winding (window : Window grid box) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding window.boundary.path = Winding.Box.Basic.quadrupledBoxWinding
      polynomial box := by
  dsimp only [boundary]
  rw [Geometry.Grid.Winding.Walk.append_winding, Geometry.Grid.Winding.Walk.append_winding,
    Geometry.Grid.Winding.Walk.append_winding,
    Geometry.Grid.Winding.Walk.reverse_winding,
    Geometry.Grid.Winding.Walk.reverse_winding,
    window.horizontal_winding, window.horizontal_winding, window.vertical_winding, window.vertical_winding,
    Winding.Box.Basic.quadrupledBoxWinding_eq]
  have top : (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial box.yUpper box.xUpper box.xLower).doubledWinding =
      -(Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial box.yUpper box.xLower box.xUpper).doubledWinding :=
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
  have left : (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial box.xLower box.yUpper box.yLower).doubledWinding =
      -(Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial box.xLower box.yLower box.yUpper).doubledWinding :=
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
  rw [top, left]
  ring1

/-- Read the retained cell selection as the Cartesian product of the actual
walk spines. This proof does not allocate a replacement cell grid at runtime. -/
theorem sum_cells (window : Window grid box) (value : Geometry.Grid.ClearGrid.Cell
  polynomial ambient → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues value window.cells =
      Geometry.Grid.CellBoundary.sumValues (fun x => Geometry.Grid.CellBoundary.sumValues (fun y => value ⟨x, y⟩)
        window.y.edges) window.x.edges := by
  have xEdges : window.x.edges = grid.xIntervals.filter
      (fun interval => decide (box.xLower ≤ interval.lower.coordinate ∧ interval.upper.coordinate ≤ box.xUpper)) :=
    Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
      (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise grid.vertical grid.vertical_ordered) window.x
  have yEdges : window.y.edges = grid.yIntervals.filter
      (fun interval => decide (box.yLower ≤ interval.lower.coordinate ∧ interval.upper.coordinate ≤ box.yUpper)) :=
    Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
      (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered) window.y
  rw [window.cells_eq, Geometry.Grid.WindowBoundary.sumValues_filter, xEdges,
    Geometry.Grid.WindowBoundary.sumValues_filter]
  change Geometry.Grid.CellBoundary.sumValues _ (grid.xIntervals.flatMap fun x => grid.yIntervals.map fun y => (⟨x, y⟩ :
    Geometry.Grid.ClearGrid.Cell polynomial ambient)) = _
  rw [Geometry.Grid.CellBoundary.sumValues_flatMap]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro x _
  rw [Geometry.Grid.CellBoundary.sumValues_map]
  by_cases xInside : box.xLower ≤ x.lower.coordinate ∧ x.upper.coordinate ≤ box.xUpper
  · rw [if_pos xInside, yEdges, Geometry.Grid.WindowBoundary.sumValues_filter]
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro y _
    by_cases yInside : box.yLower ≤ y.lower.coordinate ∧ y.upper.coordinate ≤ box.yUpper
    · have inside : (Geometry.Grid.ClearGrid.Cell.mk x y).box.Refines box := ⟨xInside.1, xInside.2, yInside⟩
      rw [if_pos inside, if_pos yInside]
    · have outside : ¬(Geometry.Grid.ClearGrid.Cell.mk x y).box.Refines box := fun inside => yInside inside.2.2
      rw [if_neg outside, if_neg yInside]
  · rw [if_neg xInside]
    trans Geometry.Grid.CellBoundary.sumValues (fun _ => 0) grid.yIntervals
    · apply Geometry.Grid.CellBoundary.sumValues_congr
      intro y _
      have outside : ¬(Geometry.Grid.ClearGrid.Cell.mk x y).box.Refines box := fun inside => xInside ⟨inside.1,
        inside.2.1⟩
      exact if_neg outside
    · exact Geometry.Grid.CellBoundary.sumValues_zero _

/-- Every internal adjacent edge cancels, while all intermediate boundary
cuts remain in the actual enclosing walk. -/
theorem sum_cells_eq_boundary (window : Window grid box) (values :
  Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues values.cellBoundary window.cells = values.walk window.boundary := by
  rw [window.sum_cells, window.boundary_value]
  let bottomTop := fun (x : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate
    (polynomial := polynomial) (ambient := ambient)))
      (y : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
        polynomial) (ambient := ambient))) =>
    values.horizontal x.lower.coordinate x.upper.coordinate y.lower.coordinate -
      values.horizontal x.lower.coordinate x.upper.coordinate y.upper.coordinate
  let rightLeft := fun (x : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate
    (polynomial := polynomial) (ambient := ambient)))
      (y : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
        polynomial) (ambient := ambient))) =>
    values.vertical x.upper.coordinate y.lower.coordinate y.upper.coordinate -
      values.vertical x.lower.coordinate y.lower.coordinate y.upper.coordinate
  have separated : Geometry.Grid.CellBoundary.sumValues (fun x => Geometry.Grid.CellBoundary.sumValues (fun y =>
    values.cellBoundary (Geometry.Grid.ClearGrid.Cell.mk x y)) window.y.edges) window.x.edges =
      Geometry.Grid.CellBoundary.sumValues (fun x => Geometry.Grid.CellBoundary.sumValues (bottomTop x) window.y.edges)
        window.x.edges +
        Geometry.Grid.CellBoundary.sumValues (fun x => Geometry.Grid.CellBoundary.sumValues (rightLeft x)
          window.y.edges) window.x.edges := by
    rw [← Geometry.Grid.CellBoundary.sumValues_add]
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro x _
    rw [← Geometry.Grid.CellBoundary.sumValues_add]
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro y _
    dsimp only [Geometry.Grid.CellBoundary.EdgeValues.cellBoundary, Geometry.Grid.ClearGrid.Cell.box, bottomTop,
      rightLeft]
    ring1
  rw [separated, Geometry.Grid.CellBoundary.sumValues_swap rightLeft window.x.edges window.y.edges]
  apply congrArg₂ (· + ·)
  · apply Geometry.Grid.CellBoundary.sumValues_congr
    intro x _
    exact Geometry.Grid.WindowAxes.IncreasingWalk.sum_differences
      (fun y => values.horizontal x.lower.coordinate x.upper.coordinate y) window.y
  · apply Geometry.Grid.CellBoundary.sumValues_congr
    intro y _
    have negative := Geometry.Grid.CellBoundary.sumValues_congr (rightLeft · y)
      (fun x => -(values.vertical x.lower.coordinate y.lower.coordinate y.upper.coordinate -
        values.vertical x.upper.coordinate y.lower.coordinate y.upper.coordinate)) window.x.edges
      (fun _ _ => by dsimp only [rightLeft]; ring1)
    rw [negative, Geometry.Grid.CellBoundary.sumValues_neg,
      Geometry.Grid.WindowAxes.IncreasingWalk.sum_differences
        (fun x => values.vertical x y.lower.coordinate y.upper.coordinate) window.x]
    ring1

end Window
end Grid
end Purelib.Polynomial.Geometry.Grid.WindowBoundary
