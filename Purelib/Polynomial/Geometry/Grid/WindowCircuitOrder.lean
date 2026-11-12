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

open Purelib.Data.Gaussian.Components
open Purelib.RootIsolation.SquareRoot.Grid

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

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

section WindowCircuits

/-- Equal retained coordinates identify the same clearance-bearing entry;
the proof fields of the two lookups then agree by proof irrelevance.

Strict ordering identifies the two retained entries at their common coordinate.
The original membership and coordinate proofs then agree by proof irrelevance. -/
theorem lookup_unique {Alpha : Type} {key : Alpha → Fraction.Rational} {entries : List Alpha} {coordinate :
  Fraction.Rational}
    (ordered : entries.Pairwise (fun first second => key first < key second))
    (first last : AxisWalks.Lookup (key := key) entries coordinate) : first = last := by
  rcases first with ⟨first, firstMember, firstEq⟩
  rcases last with ⟨last, lastMember, lastEq⟩
  have equal := Pairwise.ordered_eq ordered firstMember lastMember (firstEq.trans lastEq.symm)
  cases equal
  rfl

/-- Lift a retained increasing horizontal axis walk to its exact clear grid line.

The supplied horizontal line and finite interval walk retain their original
clearance evidence. Endpoint transport uses that same line coordinate equality. -/
@[expose]
def horizontal {first last y : Fraction.Rational} (walk : AxisWalks.IncreasingWalk grid.xIntervals first
  last)
    (line : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      :
    Walks.Walk grid (Basic.point first y) (Basic.point last y) :=
  (Walks.Walk.horizontalIncreasing line.entry line.member walk).castEndpoints
    (congrArg (Basic.point first) line.coordinate_eq) (congrArg (Basic.point
      last) line.coordinate_eq)

/-- Lift a retained increasing vertical axis walk to its exact clear grid line.

The supplied vertical line and finite interval walk retain their original
clearance evidence. Endpoint transport keeps their displayed start and finish. -/
@[expose]
def vertical {first last x : Fraction.Rational}
    (line : AxisWalks.Lookup (key := ClearGrid.VerticalLine.coordinate) grid.vertical x)
    (walk : AxisWalks.IncreasingWalk grid.yIntervals first last) :
    Walks.Walk grid (Basic.point x first) (Basic.point x last) :=
  (Walks.Walk.verticalIncreasing line.entry line.member walk).castEndpoints
    (congrArg (fun x => Basic.point x first) line.coordinate_eq) (congrArg (fun x =>
      Basic.point x last) line.coordinate_eq)

/-- Construct the vertical edge of a retained row band at a certified grid coordinate.

The original row band supplies both endpoints and its interval membership.
The retained line lookup provides the same vertical clearance-bearing edge. -/
@[expose]
def side (band : ClearGrid.Interval (ClearGrid.HorizontalLine.coordinate (polynomial :=
  polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals) {x : Fraction.Rational}
    (line : AxisWalks.Lookup (key := ClearGrid.VerticalLine.coordinate) grid.vertical x) :
    Walks.Edge grid (Basic.point x band.lower.coordinate)
      (Basic.point x band.upper.coordinate) := by
  rw [← line.coordinate_eq]
  exact .vertical band member line.entry line.member

/-- A lookup at an existing line's coordinate produces the same literal horizontal walk. -/
private theorem horizontal_entry {first last : Fraction.Rational}
    (walk : AxisWalks.IncreasingWalk grid.xIntervals first last)
    (entry : ClearGrid.HorizontalLine polynomial ambient) (member : entry ∈ grid.horizontal)
    (line : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate) grid.horizontal
      entry.coordinate) :
    horizontal walk line = Walks.Walk.horizontalIncreasing entry member walk := by
  rcases line with ⟨actual, actualMember, coordinateEq⟩
  have equal := Pairwise.ordered_eq grid.horizontal_ordered actualMember member coordinateEq
  subst actual
  rfl

/-- Lifting an empty horizontal axis walk gives the stationary grid walk. -/
private theorem horizontal_nil {x y : Fraction.Rational}
    (line : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
      :
    horizontal (.nil x) line = Walks.Walk.nil (Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- Lifting an empty vertical axis walk gives the stationary grid walk. -/
private theorem vertical_nil {x y : Fraction.Rational}
    (line : AxisWalks.Lookup (key := ClearGrid.VerticalLine.coordinate) grid.vertical x) :
    vertical line (.nil y) = Walks.Walk.nil (Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- Lifting a vertical axis step prepends the original band-side edge. -/
private theorem vertical_cons {x finish : Fraction.Rational}
    (line : AxisWalks.Lookup (key := ClearGrid.VerticalLine.coordinate) grid.vertical x)
    (band : ClearGrid.Interval (ClearGrid.HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals)
    (tail : AxisWalks.IncreasingWalk grid.yIntervals band.upper.coordinate finish) :
    vertical line (.cons band member tail) = .cons (side band member
      line) (vertical line tail) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- An increasing axis walk contains no repeated intervals.

Every tail edge starts at or above the current interval finish. The strict
order of the current interval excludes a second occurrence in that tail. -/
private theorem axis_unique {Alpha : Type} {key : Alpha → Fraction.Rational} {intervals : List
  (ClearGrid.Interval key)} :
    {first last : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk intervals first last) →
      walk.edges.Nodup
  | _, _, .nil _ => .nil
  | _, _, .cons interval member tail => by
      refine List.pairwise_cons.mpr ⟨?_, WindowCircuits.axis_unique
        tail⟩
      intro entry belongs same
      cases same
      exact (not_lt_of_ge (tail.edge_bounds interval belongs).1) interval.ordered

/-- The row-major Cartesian product of two duplicate-free interval lists contains no repeated cells.

The original horizontal and vertical interval lists are individually unique.
Cell projections identify both coordinates, excluding duplicates across bands. -/
private theorem product_unique
    (xs : List (ClearGrid.Interval (ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient))))
    (ys : List (ClearGrid.Interval (ClearGrid.HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient))))
    (xUnique : xs.Nodup) (yUnique : ys.Nodup) :
    (ys.flatMap fun band => xs.map (fun interval => ClearGrid.Cell.mk interval band)).Nodup := by
  induction ys with
  | nil => exact .nil
  | cons band tail ih =>
      rw [Flatten.flatMap_cons]
      refine Nodup.nodup_append
        (Nodup.nodup_map_of_injective (fun _ _ equal => congrArg ClearGrid.Cell.horizontal
          equal)
          xUnique)
        (ih (List.pairwise_cons.mp yUnique).2) ?_
      intro first firstMember last lastMember equal
      obtain ⟨x, _, firstEq⟩ := Map.mem_map.mp firstMember
      obtain ⟨y, yMember, lastMember⟩ := Flatten.mem_flatMap.mp lastMember
      obtain ⟨z, _, lastEq⟩ := Map.mem_map.mp lastMember
      have bands : band = y := congrArg ClearGrid.Cell.vertical (firstEq.trans (equal.trans lastEq.symm))
      exact (List.pairwise_cons.mp yUnique).1 y yMember bands

variable {left right : Fraction.Rational} (x : AxisWalks.IncreasingWalk grid.xIntervals left right)
  (leftLine : AxisWalks.Lookup (key := ClearGrid.VerticalLine.coordinate) grid.vertical
    left)
  (rightLine : AxisWalks.Lookup (key := ClearGrid.VerticalLine.coordinate) grid.vertical
    right)

/-- Construct the cell-circuit tree for successive retained row bands.

Each row uses its right-to-left circuit order, and later rows are based through the actual left-side connector. -/
@[expose]
def ofWalk : {bottom top : Fraction.Rational} → AxisWalks.IncreasingWalk grid.yIntervals bottom top →
    RowCircuitOrder.CellCircuits grid (Basic.point left bottom)
  | _, _, .nil bottom => .nil (Basic.point left bottom)
  | _, _, .cons band member tail =>
      .append (RowCircuitOrder.RowCircuits.ofWalk band member x)
        ((WindowCircuits.ofWalk tail).based (.cons
          (side band member leftLine) (.nil _)))

/-- The circuit tree retains the row-major cell list with reversed horizontal order in every row.

Each retained row contributes its original reversed horizontal interval list.
The circuit tree appends those row lists in the original increasing row order. -/
theorem ofWalk_cells : {bottom top : Fraction.Rational} → (y : AxisWalks.IncreasingWalk grid.yIntervals
  bottom top) →
    (ofWalk x leftLine y).cells = y.edges.flatMap (fun band =>
      x.edges.reverse.map (fun interval => ClearGrid.Cell.mk interval band))
  | _, _, .nil _ => rfl
  | _, _, .cons band member tail => by
      simp only [ofWalk,
        RowCircuitOrder.CellCircuits.cells, RowCircuitOrder.CellCircuits.based_cells,
        RowCircuitOrder.RowCircuits.ofWalk_cells,
        WindowCircuits.ofWalk_cells tail,
          AxisWalks.IncreasingWalk.edges, Flatten.flatMap_cons, -eq_self, -iff_self]
      rfl

/-- Every retained row visits the actual horizontal intervals from right to left.

The original increasing walk bounds each later interval above the current
upper endpoint. Reversal puts those same intervals before the current
one, retaining their clearance-bearing payloads and original memberships.
-/
private theorem row_pairwise
    (band : ClearGrid.Interval (ClearGrid.HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient))) :
    {first last : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk grid.xIntervals first last) →
      (walk.edges.reverse.map (fun interval => ClearGrid.Cell.mk interval band)).Pairwise
        (fun first last => first.vertical = last.vertical ∧
          ClearGrid.Interval.Before last.horizontal first.horizontal)
  | _, _, .nil _ => .nil
  | _, _, .cons interval member tail => by
      rewrite [AxisWalks.IncreasingWalk.edges, Reverse.reverse_cons, Map.map_append]
      exact Pairwise.pairwise_append (row_pairwise band tail)
        (Pairwise.pairwise_singleton _ (ClearGrid.Cell.mk interval band)) (by
          intro first firstMember last lastMember
          have lastEq := Membership.mem_singleton.mp lastMember
          subst last
          obtain ⟨actual, actualMember, equal⟩ := Map.mem_map.mp firstMember
          subst first
          exact ⟨rfl, (tail.edge_bounds actual ((Reverse.mem_reverse _).mp actualMember)).1⟩)

/-- The retained Cartesian circuit list visits later rows upward and each row right to left.

The original two interval walks supply all scalar ordering bounds. Each
cell retains its exact horizontal and vertical interval payloads; no
coordinate sorting or face classification is performed again.
-/
private theorem product_pairwise
    {left right : Fraction.Rational} (x : AxisWalks.IncreasingWalk grid.xIntervals left right) :
    {bottom top : Fraction.Rational} → (y : AxisWalks.IncreasingWalk grid.yIntervals bottom top) →
      (y.edges.flatMap (fun band => x.edges.reverse.map (fun interval => ClearGrid.Cell.mk interval band))).Pairwise
        (fun first last => ClearGrid.Interval.Before first.vertical last.vertical ∨
          first.vertical = last.vertical ∧ ClearGrid.Interval.Before last.horizontal first.horizontal)
  | _, _, .nil _ => .nil
  | _, _, .cons band member tail => by
      change ((x.edges.reverse.map (fun interval => ClearGrid.Cell.mk interval band)) ++
        tail.edges.flatMap (fun row => x.edges.reverse.map (fun interval => ClearGrid.Cell.mk interval row))).Pairwise _
      refine Pairwise.pairwise_append ?_ (product_pairwise x tail) ?_
      · exact List.Pairwise.imp (fun related => Or.inr related) (row_pairwise band x)
      · intro first firstMember last lastMember
        obtain ⟨horizontal, _, firstEq⟩ := Map.mem_map.mp firstMember
        obtain ⟨vertical, verticalMember, lastMember⟩ := Flatten.mem_flatMap.mp lastMember
        obtain ⟨otherHorizontal, _, lastEq⟩ := Map.mem_map.mp lastMember
        subst first
        subst last
        exact Or.inl (tail.edge_bounds vertical verticalMember).1

/-- Build the positive rectangle boundary from the two retained axis walks and four clear-line lookups. -/
@[expose]
def boundary {bottom top : Fraction.Rational} (y : AxisWalks.IncreasingWalk grid.yIntervals bottom top)
    (bottomLine : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate)
      grid.horizontal bottom)
    (topLine : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate) grid.horizontal
      top) :
    Walks.Walk grid (Basic.point left bottom) (Basic.point left
      bottom) :=
  Walks.Walk.rectangle (horizontal x bottomLine) (vertical rightLine y) (horizontal x topLine) (vertical
    leftLine y)

/-- Compare the ordered circuit product with its rectangle boundary on the lifted edge bank.

Successive row sewing cancels the actual seam traversals while preserving arriving sheets and indexed edge words. -/
theorem comparison {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    {bottom top : Fraction.Rational} → (y : AxisWalks.IncreasingWalk grid.yIntervals bottom top) →
    (bottomLine : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate)
      grid.horizontal bottom) →
    (topLine : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate) grid.horizontal
      top) →
    RootEdgeBank.ChainComparison edges vertices
      (ofWalk x leftLine y).product
      (boundary x leftLine rightLine y bottomLine topLine)
  | _, _, .nil _, bottomLine, topLine => by
      have same : horizontal x bottomLine = horizontal x topLine := by
        rcases topLine with ⟨entry, member, rfl⟩
        exact horizontal_entry x entry member bottomLine
      simp only [ofWalk,
        RowCircuitOrder.CellCircuits.product, boundary,
        vertical_nil, Walks.Walk.rectangle,
        Walks.Walk.append, Walks.Walk.reverse, Walks.Walk.reverseOnto,
          Walks.Walk.append_nil, -eq_self, -iff_self]
      rw [same]
      exact (RootEdgeBank.ChainComparison.retrace reference
        (horizontal x topLine)).symm
  | _, _, .cons band member tail, bottomLine, topLine => by
      let seam : AxisWalks.Lookup (key := ClearGrid.HorizontalLine.coordinate)
        grid.horizontal band.upper.coordinate :=
        ⟨band.upper, (ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered member).2, rfl⟩
      let leftSide : Walks.Walk grid (Basic.point left band.lower.coordinate)
        (Basic.point left band.upper.coordinate) :=
        .cons (side band member leftLine) (.nil _)
      let rightSide : Walks.Walk grid (Basic.point right band.lower.coordinate)
        (Basic.point right band.upper.coordinate) :=
        .cons (side band member rightLine) (.nil _)
      have row := RowCircuitOrder.RowCircuits.comparison (edges := edges) (vertices := vertices) band
        member reference x
        (side band member leftLine)
          (side band member rightLine)
      have rest := WindowCircuits.comparison (edges := edges)
        (vertices := vertices) reference tail seam topLine
      have based := ((ofWalk x leftLine tail).based_product reference
        leftSide).trans (rest.based leftSide)
      have sewn := RootEdgeBank.ChainComparison.vertical_sewing
        (edges := edges) (vertices := vertices) reference
        (RowCircuitOrder.RowCircuits.bottom band member x) rightSide (vertical rightLine tail) (horizontal
          x topLine)
        (vertical leftLine tail) leftSide (RowCircuitOrder.RowCircuits.top band member x)
      apply (row.append based).trans (sewn.trans
        (RootEdgeBank.ChainComparison.of_eq ?_))
      simp only [boundary,
        horizontal_entry x band.lower
        (ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered member).1,
        vertical_cons, Walks.Walk.rectangle,
          Walks.Walk.append, leftSide, rightSide, RowCircuitOrder.RowCircuits.bottom,
          -eq_self, -iff_self]
      rfl

end WindowCircuits

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

-- Retain the original nominal Window API; its repeated Grid component predates this proof cut.
namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
variable {box : Box} (window : Window grid box)

/-- Build the ordered cell circuits based at the window's southwest corner.

Rows proceed upward and each row visits its cells from right to left. -/
@[expose]
def circuits : RowCircuitOrder.CellCircuits grid (Basic.point box.xLower box.yLower)
  := WindowCircuitOrder.WindowCircuits.ofWalk window.x window.left window.y

/-- Read the circuit cells as rows from bottom to top, with each row's horizontal intervals reversed.

The circuit construction follows the retained vertical walk and reverses each
retained horizontal edge list. The equation displays the same original cells in that order. -/
theorem circuits_cells : window.circuits.cells =
    window.y.edges.flatMap (fun band => window.x.edges.reverse.map (fun interval => ClearGrid.Cell.mk
      interval band)) :=
  WindowCircuitOrder.WindowCircuits.ofWalk_cells window.x window.left window.y

/-- No original cell occurs twice in the window's ordered circuit list.

Axis-walk interval bounds exclude repeated intervals. Their row-major product
therefore has no repeated original grid cell. -/
theorem circuits_unique : window.circuits.cells.Nodup := by
  rw [window.circuits_cells]
  exact WindowCircuitOrder.WindowCircuits.product_unique _ _ (Nodup.reverse
    (WindowCircuitOrder.WindowCircuits.axis_unique window.x))
    (WindowCircuitOrder.WindowCircuits.axis_unique window.y)

/-- The ordered cell-circuit product agrees with the window boundary on the retained lifted edge bank.

The comparison preserves both arriving sheets and their finite retracing-word relations. -/
theorem circuits_comparison {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    RootEdgeBank.ChainComparison edges vertices
      window.circuits.product window.boundary :=
  WindowCircuitOrder.WindowCircuits.comparison window.x window.left window.right reference window.y
    window.bottom window.top

/-- The geometric order includes every selected original cell and no cell
outside the window. This includes windows of zero width or zero height.

The original window axis filters retain exactly their bounded grid intervals.
Their Cartesian cells give both refinement bounds and original grid membership. -/
theorem circuits_member {cell : ClearGrid.Cell polynomial ambient} :
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
    have intervals := CellBoundary.Cell.intervals_mem cell member
    have horizontal : cell.horizontal ∈ window.x.edges := by
      exact (WindowAxes.IncreasingWalk.edges_eq_filter
        (ClearGrid.Interval.adjacent_pairwise grid.vertical grid.vertical_ordered) window.x).symm ▸
        Filter.mem_filter.mpr ⟨intervals.1, decide_eq_true ⟨inside.1, inside.2.1⟩⟩
    have vertical : cell.vertical ∈ window.y.edges := by
      exact (WindowAxes.IncreasingWalk.edges_eq_filter
        (ClearGrid.Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered) window.y).symm ▸
        Filter.mem_filter.mpr ⟨intervals.2, decide_eq_true inside.2.2⟩
    exact Flatten.mem_flatMap.mpr ⟨cell.vertical, vertical,
      Map.mem_map.mpr ⟨cell.horizontal, (Reverse.mem_reverse _).mpr horizontal, rfl⟩⟩

/-- The original window circuits retain their actual upward-row and right-to-left order.

The scalar relation reads the original interval payloads. It remains valid
for all retained cells, including cells sharing a boundary line, and
therefore transports to any order-preserving selected occurrence list.
-/
theorem circuits_pairwise :
    window.circuits.cells.Pairwise
      (fun first last => ClearGrid.Interval.Before first.vertical last.vertical ∨
        first.vertical = last.vertical ∧ ClearGrid.Interval.Before last.horizontal first.horizontal) := by
  rewrite [window.circuits_cells]
  exact WindowCircuitOrder.WindowCircuits.product_pairwise window.x window.y

end Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

namespace Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
variable {box : Box} (window : WindowBoundary.Window grid box)

set_option genInjectivity false in
/-- Retain an ordered cell-circuit tree, its cell list and lifted product.

The window selection, ordered readback and lifted comparison refer to these
exact cached values, with the original grid and edge-bank owners retained. -/
structure CircuitOrder {frames : RootFrames grid} (edges :
  RootEdgeBank frames) (vertices :
  LiftedVertices.VertexBank grid) where
  /-- The retained ordered tree of original grid-cell circuits. -/ tree : RowCircuitOrder.CellCircuits
    grid (Basic.point box.xLower box.yLower)
  /-- The retained tree is the window's constructed circuit tree. -/ tree_eq : tree = window.circuits
  /-- The cached cell list read from the retained tree. -/ cells : List (ClearGrid.Cell polynomial
    ambient)
  /-- The cached cells are exactly those of the retained tree. -/ cells_eq : cells = tree.cells
  /-- The cached list visits rows upward and each row from right to left. -/ order : cells = window.y.edges.flatMap (fun
    band => window.x.edges.reverse.map (fun interval => ClearGrid.Cell.mk interval band))
  /-- The cached cells are exactly the original grid cells refining the window. -/ selected : ∀ cell, cell ∈ cells ↔
    cell ∈ grid.cells ∧ cell.box.Refines box
  /-- The cached based product of the retained cell circuits. -/ product : Walks.Walk grid
    (Basic.point box.xLower box.yLower) (Basic.point box.xLower box.yLower)
  /-- The cached walk is the retained tree's actual circuit product. -/ product_eq : product = tree.product
  /-- The cached product and window boundary agree on sheets and indexed edge words. -/ comparison :
    RootEdgeBank.ChainComparison edges vertices product
    window.boundary

constructive_injectivity CircuitOrder

/-- Cache the window's ordered circuit tree, cell list and product walk once.

The retained equalities, selection predicate and lifted comparison all refer to these exact cached values. -/
@[expose]
def prepareCircuits {frames : RootFrames grid} (edges :
  RootEdgeBank frames) (vertices :
  LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    CircuitOrder window edges vertices :=
  let tree := window.circuits
  ⟨tree, rfl, tree.cells, rfl, window.circuits_cells, fun _ => window.circuits_member,
    tree.product, rfl, window.circuits_comparison reference⟩

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

end
