module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Data.List.Reverse
import Purelib.Data.List.Pairwise
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
public import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.WindowAxes
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement

public section

/-!
# Ordered actual cell circuits for a retained rectangular window

Rows run from bottom to top, and each row runs from right to left. The
connectors follow the left side and then the bottom of the selected row.
The comparison preserves the actual root sheet and lifted-edge values.
-/

section

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

section WindowCircuits

/-- Equal retained coordinates identify the same clearance-bearing entry;
the proof fields of the two lookups then agree by proof irrelevance.

Strict ordering identifies the two retained entries at their common coordinate.
The original membership and coordinate proofs then agree by proof irrelevance. -/
theorem lookup_unique {Alpha : Type} {key : Alpha → Fraction.Rational} {entries : List Alpha} {coordinate :
  Fraction.Rational}
    (ordered : entries.Pairwise (fun first second => key first < key second))
    (first last : Geometry.Grid.AxisWalks.Lookup (key := key) entries coordinate) : first = last := by
  rcases first with ⟨first, firstMember, firstEq⟩
  rcases last with ⟨last, lastMember, lastEq⟩
  have equal := Pairwise.ordered_eq ordered firstMember lastMember (firstEq.trans lastEq.symm)
  cases equal
  rfl

/-- Lift a retained increasing horizontal axis walk to its exact clear grid line.

The supplied horizontal line and finite interval walk retain their original
clearance evidence. Endpoint transport uses that same line coordinate equality. -/
@[expose]
def horizontal {first last y : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals first
  last)
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point first y) (Gaussian.Components.Basic.point last y) :=
  (Geometry.Grid.Walks.Walk.horizontalIncreasing line.entry line.member walk).castEndpoints
    (congrArg (Gaussian.Components.Basic.point first) line.coordinate_eq) (congrArg (Gaussian.Components.Basic.point
      last) line.coordinate_eq)

/-- Lift a retained increasing vertical axis walk to its exact clear grid line.

The supplied vertical line and finite interval walk retain their original
clearance evidence. Endpoint transport keeps their displayed start and finish. -/
@[expose]
def vertical {first last x : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x)
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals first last) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point x first) (Gaussian.Components.Basic.point x last) :=
  (Geometry.Grid.Walks.Walk.verticalIncreasing line.entry line.member walk).castEndpoints
    (congrArg (fun x => Gaussian.Components.Basic.point x first) line.coordinate_eq) (congrArg (fun x =>
      Gaussian.Components.Basic.point x last) line.coordinate_eq)

/-- Construct the vertical edge of a retained row band at a certified grid coordinate.

The original row band supplies both endpoints and its interval membership.
The retained line lookup provides the same vertical clearance-bearing edge. -/
@[expose]
def side (band : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
  polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals) {x : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x) :
    Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point x band.lower.coordinate)
      (Gaussian.Components.Basic.point x band.upper.coordinate) := by
  rw [← line.coordinate_eq]
  exact .vertical band member line.entry line.member

/-- A lookup at an existing line's coordinate produces the same literal horizontal walk. -/
private theorem horizontal_entry {first last : Fraction.Rational}
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals first last)
    (entry : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : entry ∈ grid.horizontal)
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal
      entry.coordinate) :
    horizontal walk line = Geometry.Grid.Walks.Walk.horizontalIncreasing entry member walk := by
  rcases line with ⟨actual, actualMember, coordinateEq⟩
  have equal := Pairwise.ordered_eq grid.horizontal_ordered actualMember member coordinateEq
  subst actual
  rfl

/-- Lifting an empty horizontal axis walk gives the stationary grid walk. -/
private theorem horizontal_nil {x y : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      :
    horizontal (.nil x) line = Geometry.Grid.Walks.Walk.nil (Gaussian.Components.Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- Lifting an empty vertical axis walk gives the stationary grid walk. -/
private theorem vertical_nil {x y : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x) :
    vertical line (.nil y) = Geometry.Grid.Walks.Walk.nil (Gaussian.Components.Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- Lifting a vertical axis step prepends the original band-side edge. -/
private theorem vertical_cons {x finish : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x)
    (band : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals)
    (tail : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals band.upper.coordinate finish) :
    vertical line (.cons band member tail) = .cons (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member
      line) (vertical line tail) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- An increasing axis walk contains no repeated intervals.

Every tail edge starts at or above the current interval finish. The strict
order of the current interval excludes a second occurrence in that tail. -/
private theorem axis_unique {Alpha : Type} {key : Alpha → Fraction.Rational} {intervals : List
  (Geometry.Grid.ClearGrid.Interval key)} :
    {first last : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) →
      walk.edges.Nodup
  | _, _, .nil _ => .nil
  | _, _, .cons interval member tail => by
      refine List.pairwise_cons.mpr ⟨?_, Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.axis_unique
        tail⟩
      intro entry belongs same
      cases same
      exact (not_lt_of_ge (tail.edge_bounds interval belongs).1) interval.ordered

/-- The row-major Cartesian product of two duplicate-free interval lists contains no repeated cells.

The original horizontal and vertical interval lists are individually unique.
Cell projections identify both coordinates, excluding duplicates across bands. -/
private theorem product_unique
    (xs : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient))))
    (ys : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient))))
    (xUnique : xs.Nodup) (yUnique : ys.Nodup) :
    (ys.flatMap fun band => xs.map (fun interval => Geometry.Grid.ClearGrid.Cell.mk interval band)).Nodup := by
  induction ys with
  | nil => exact .nil
  | cons band tail ih =>
      rw [Flatten.flatMap_cons]
      refine Nodup.nodup_append
        (Data.List.Nodup.nodup_map_of_injective (fun _ _ equal => congrArg Geometry.Grid.ClearGrid.Cell.horizontal
          equal)
          xUnique)
        (ih (List.pairwise_cons.mp yUnique).2) ?_
      intro first firstMember last lastMember equal
      obtain ⟨x, _, firstEq⟩ := Map.mem_map.mp firstMember
      obtain ⟨y, yMember, lastMember⟩ := Flatten.mem_flatMap.mp lastMember
      obtain ⟨z, _, lastEq⟩ := Map.mem_map.mp lastMember
      have bands : band = y := congrArg Geometry.Grid.ClearGrid.Cell.vertical (firstEq.trans (equal.trans lastEq.symm))
      exact (List.pairwise_cons.mp yUnique).1 y yMember bands

variable {left right : Fraction.Rational} (x : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals left right)
  (leftLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical
    left)
  (rightLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical
    right)

/-- Construct the cell-circuit tree for successive retained row bands.

Each row uses its right-to-left circuit order, and later rows are based through the actual left-side connector. -/
@[expose]
def ofWalk : {bottom top : Fraction.Rational} → Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals bottom top →
    Geometry.Grid.RowCircuitOrder.CellCircuits grid (Gaussian.Components.Basic.point left bottom)
  | _, _, .nil bottom => .nil (Gaussian.Components.Basic.point left bottom)
  | _, _, .cons band member tail =>
      .append (Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member x)
        ((Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk tail).based (.cons
          (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member leftLine) (.nil _)))

/-- The circuit tree retains the row-major cell list with reversed horizontal order in every row.

Each retained row contributes its original reversed horizontal interval list.
The circuit tree appends those row lists in the original increasing row order. -/
theorem ofWalk_cells : {bottom top : Fraction.Rational} → (y : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals
  bottom top) →
    (Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk x leftLine y).cells = y.edges.flatMap (fun band =>
      x.edges.reverse.map (fun interval => Geometry.Grid.ClearGrid.Cell.mk interval band))
  | _, _, .nil _ => rfl
  | _, _, .cons band member tail => by
      simp only [Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk,
        Geometry.Grid.RowCircuitOrder.CellCircuits.cells, Geometry.Grid.RowCircuitOrder.CellCircuits.based_cells,
        Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk_cells,
        Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk_cells tail,
          Geometry.Grid.AxisWalks.IncreasingWalk.edges, Flatten.flatMap_cons, -eq_self, -iff_self]
      rfl

/-- Build the positive rectangle boundary from the two retained axis walks and four clear-line lookups. -/
@[expose]
def boundary {bottom top : Fraction.Rational} (y : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals bottom top)
    (bottomLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      grid.horizontal bottom)
    (topLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal
      top) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point left bottom) (Gaussian.Components.Basic.point left
      bottom) :=
  Geometry.Grid.Walks.Walk.rectangle (horizontal x bottomLine) (vertical rightLine y) (horizontal x topLine) (vertical
    leftLine y)

/-- Compare the ordered circuit product with its rectangle boundary on the lifted edge bank.

Successive row sewing cancels the actual seam traversals while preserving arriving sheets and indexed edge words. -/
theorem comparison {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    {bottom top : Fraction.Rational} → (y : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals bottom top) →
    (bottomLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      grid.horizontal bottom) →
    (topLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal
      top) →
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk x leftLine y).product
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary x leftLine rightLine y bottomLine topLine)
  | _, _, .nil _, bottomLine, topLine => by
      have same : horizontal x bottomLine = horizontal x topLine := by
        rcases topLine with ⟨entry, member, rfl⟩
        exact Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal_entry x entry member bottomLine
      simp only [Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk,
        Geometry.Grid.RowCircuitOrder.CellCircuits.product, Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary,
        Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical_nil, Geometry.Grid.Walks.Walk.rectangle,
        Geometry.Grid.Walks.Walk.append, Geometry.Grid.Walks.Walk.reverse, Geometry.Grid.Walks.Walk.reverseOnto,
          Polynomial.Geometry.Grid.Walks.Walk.append_nil, -eq_self, -iff_self]
      rw [same]
      exact (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.retrace reference
        (horizontal x topLine)).symm
  | _, _, .cons band member tail, bottomLine, topLine => by
      let seam : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
        grid.horizontal band.upper.coordinate :=
        ⟨band.upper, (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered member).2, rfl⟩
      let leftSide : Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point left band.lower.coordinate)
        (Gaussian.Components.Basic.point left band.upper.coordinate) :=
        .cons (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member leftLine) (.nil _)
      let rightSide : Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point right band.lower.coordinate)
        (Gaussian.Components.Basic.point right band.upper.coordinate) :=
        .cons (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member rightLine) (.nil _)
      have row := Geometry.Grid.RowCircuitOrder.RowCircuits.comparison (edges := edges) (vertices := vertices) band
        member reference x
        (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member leftLine)
          (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member rightLine)
      have rest := Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.comparison (edges := edges)
        (vertices := vertices) reference tail seam topLine
      have based := ((Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk x leftLine tail).based_product reference
        leftSide).trans (rest.based leftSide)
      have sewn := RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.vertical_sewing
        (edges := edges) (vertices := vertices) reference
        (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band member x) rightSide (vertical rightLine tail) (horizontal
          x topLine)
        (vertical leftLine tail) leftSide (Geometry.Grid.RowCircuitOrder.RowCircuits.top band member x)
      apply (row.append based).trans (sewn.trans
        (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_))
      simp only [Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary,
        Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal_entry x band.lower
        (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered member).1,
        Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical_cons, Geometry.Grid.Walks.Walk.rectangle,
          Geometry.Grid.Walks.Walk.append, leftSide, rightSide, Geometry.Grid.RowCircuitOrder.RowCircuits.bottom,
          -eq_self, -iff_self]
      rfl

end WindowCircuits

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

-- Retain the original nominal Window API; its repeated Grid component predates this proof cut.
namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
variable {box : Box} (window : Window grid box)

/-- Build the ordered cell circuits based at the window's southwest corner.

Rows proceed upward and each row visits its cells from right to left. -/
@[expose]
def circuits : Geometry.Grid.RowCircuitOrder.CellCircuits grid (Gaussian.Components.Basic.point box.xLower box.yLower)
  := Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk window.x window.left window.y

/-- Read the circuit cells as rows from bottom to top, with each row's horizontal intervals reversed.

The circuit construction follows the retained vertical walk and reverses each
retained horizontal edge list. The equation displays the same original cells in that order. -/
theorem circuits_cells : window.circuits.cells =
    window.y.edges.flatMap (fun band => window.x.edges.reverse.map (fun interval => Geometry.Grid.ClearGrid.Cell.mk
      interval band)) :=
  Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk_cells window.x window.left window.y

/-- No original cell occurs twice in the window's ordered circuit list.

Axis-walk interval bounds exclude repeated intervals. Their row-major product
therefore has no repeated original grid cell. -/
theorem circuits_unique : window.circuits.cells.Nodup := by
  rw [window.circuits_cells]
  exact Geometry.Grid.WindowCircuitOrder.WindowCircuits.product_unique _ _ (Nodup.reverse
    (Geometry.Grid.WindowCircuitOrder.WindowCircuits.axis_unique window.x))
    (Geometry.Grid.WindowCircuitOrder.WindowCircuits.axis_unique window.y)

/-- The ordered cell-circuit product agrees with the window boundary on the retained lifted edge bank.

The comparison preserves both arriving sheets and their finite retracing-word relations. -/
theorem circuits_comparison {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      window.circuits.product window.boundary :=
  Geometry.Grid.WindowCircuitOrder.WindowCircuits.comparison window.x window.left window.right reference window.y
    window.bottom window.top

/-- The geometric order includes every selected original cell and no cell
outside the window. This includes windows of zero width or zero height.

The original window axis filters retain exactly their bounded grid intervals.
Their Cartesian cells give both refinement bounds and original grid membership. -/
theorem circuits_member {cell : Geometry.Grid.ClearGrid.Cell polynomial ambient} :
    cell ∈ window.circuits.cells ↔ cell ∈ grid.cells ∧ cell.box.Refines box := by
  rw [window.circuits_cells]
  constructor
  · intro member
    obtain ⟨band, bandMember, member⟩ := Flatten.mem_flatMap.mp member
    obtain ⟨interval, intervalMember, equal⟩ := Map.mem_map.mp member
    have intervalMember := (Reverse.mem_reverse _).mp intervalMember
    rw [← equal]
    exact ⟨Flatten.mem_flatMap.mpr ⟨interval, window.x.edge_mem interval intervalMember,
      Map.mem_map.mpr ⟨band, window.y.edge_mem band bandMember, rfl⟩⟩,
      (window.x.edge_bounds interval intervalMember).1, (window.x.edge_bounds interval intervalMember).2,
      window.y.edge_bounds band bandMember⟩
  · rintro ⟨member, inside⟩
    have intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
    have horizontal : cell.horizontal ∈ window.x.edges := by
      exact (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
        (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise grid.vertical grid.vertical_ordered) window.x).symm ▸
        Filter.mem_filter.mpr ⟨intervals.1, decide_eq_true ⟨inside.1, inside.2.1⟩⟩
    have vertical : cell.vertical ∈ window.y.edges := by
      exact (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
        (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered) window.y).symm ▸
        Filter.mem_filter.mpr ⟨intervals.2, decide_eq_true inside.2.2⟩
    exact Flatten.mem_flatMap.mpr ⟨cell.vertical, vertical,
      Map.mem_map.mpr ⟨cell.horizontal, (Reverse.mem_reverse _).mpr horizontal, rfl⟩⟩

end Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

namespace Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
variable {box : Box} (window : WindowBoundary.Window grid box)

set_option genInjectivity false in
/-- Retain an ordered cell-circuit tree, its cell list and lifted product.

The window selection, ordered readback and lifted comparison refer to these
exact cached values, with the original grid and edge-bank owners retained. -/
structure CircuitOrder {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid) where
  /-- The retained ordered tree of original grid-cell circuits. -/ tree : Geometry.Grid.RowCircuitOrder.CellCircuits
    grid (Gaussian.Components.Basic.point box.xLower box.yLower)
  /-- The retained tree is the window's constructed circuit tree. -/ tree_eq : tree = window.circuits
  /-- The cached cell list read from the retained tree. -/ cells : List (Geometry.Grid.ClearGrid.Cell polynomial
    ambient)
  /-- The cached cells are exactly those of the retained tree. -/ cells_eq : cells = tree.cells
  /-- The cached list visits rows upward and each row from right to left. -/ order : cells = window.y.edges.flatMap (fun
    band => window.x.edges.reverse.map (fun interval => Geometry.Grid.ClearGrid.Cell.mk interval band))
  /-- The cached cells are exactly the original grid cells refining the window. -/ selected : ∀ cell, cell ∈ cells ↔
    cell ∈ grid.cells ∧ cell.box.Refines box
  /-- The cached based product of the retained cell circuits. -/ product : Geometry.Grid.Walks.Walk grid
    (Gaussian.Components.Basic.point box.xLower box.yLower) (Gaussian.Components.Basic.point box.xLower box.yLower)
  /-- The cached walk is the retained tree's actual circuit product. -/ product_eq : product = tree.product
  /-- The cached product and window boundary agree on sheets and indexed edge words. -/ comparison :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices product
    window.boundary

constructive_injectivity CircuitOrder

/-- Cache the window's ordered circuit tree, cell list and product walk once.

The retained equalities, selection predicate and lifted comparison all refer to these exact cached values. -/
@[expose]
def prepareCircuits {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    Geometry.Grid.WindowCircuitOrder.CircuitOrder window edges vertices :=
  let tree := window.circuits
  ⟨tree, rfl, tree.cells, rfl, window.circuits_cells, fun _ => window.circuits_member,
    tree.product, rfl, window.circuits_comparison reference⟩

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

end
