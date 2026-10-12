module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Paths.OwnerLoopMonodromy
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Polynomial.Geometry.Grid.WindowAxes
-- Exposed row constructors retain the original public grid-cell certificate.
public import Purelib.Polynomial.Geometry.Grid.EdgeSides

public section

/-!
# The actual cell-circuit order in a rectangular grid row

The retained increasing axis is read from right to left. Each leaf is the
original cell boundary, based along the actual bottom-row stem. Sewing
proves agreement with the strip boundary on every initial sheet and every
antisymmetric lifted-edge valuation. Branch and regular cells both remain.
-/

namespace Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib
open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid.EdgeSides (EdgeCell)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

set_option genInjectivity false in
/-- A finite ordered expression of based cell boundaries.

Every leaf retains its original cell, grid membership and literal connector.
Append nodes retain the ordered child expressions at their common base. -/
inductive CellCircuits (grid : ClearGrid polynomial ambient) : Gaussian.Basic.Canonical → Type
  /-- The empty circuit expression at a displayed base vertex. -/ | nil (base : Gaussian.Basic.Canonical) :
    Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits grid base
  /-- One actual cell boundary, with its grid membership and connector from the common base. -/ | cell {base :
    Gaussian.Basic.Canonical} (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells)
      (stem : Geometry.Grid.Walks.Walk grid base cell.box.anchor) :
        Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits grid base
  /-- An ordered concatenation of two circuit expressions at the same base. -/ | append {base :
    Gaussian.Basic.Canonical} (first last : Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits grid base) :
    Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits grid base

constructive_injectivity CellCircuits

namespace CellCircuits

/-- Materialize the ordered circuit expression as a closed grid walk.

Each cell consumes its retained connector and original boundary; append nodes preserve circuit order. -/
@[expose] def product {base : Gaussian.Basic.Canonical} : Geometry.Grid.RowCircuitOrder.CellCircuits grid base →
  Geometry.Grid.Walks.Walk grid base base
  | .nil _ => .nil base
  | .cell face member stem => stem.based (Geometry.Grid.CellBoundary.Cell.boundaryWalk face member)
  | .append first last => first.product.append last.product
termination_by structural tree => tree

/-- Read the cells in circuit-expression order, preserving every displayed occurrence.

Each retained leaf contributes its original cell once. Appending expressions concatenates their retained cell lists
without sorting or deduplication. -/
@[expose] def cells {base : Gaussian.Basic.Canonical} : Geometry.Grid.RowCircuitOrder.CellCircuits grid base → List
  (Geometry.Grid.ClearGrid.Cell polynomial ambient)
  | .nil _ => []
  | .cell face _ _ => [face]
  | .append first last => first.cells ++ last.cells
termination_by structural tree => tree

/-- Transport a circuit expression to a new base along a supplied grid stem.

The stem is prepended to every retained connector without changing the underlying cells. -/
@[expose] def based {first last : Gaussian.Basic.Canonical} (stem : Geometry.Grid.Walks.Walk grid first last) :
  Geometry.Grid.RowCircuitOrder.CellCircuits grid last → Geometry.Grid.RowCircuitOrder.CellCircuits grid first
  | .nil _ => .nil first
  | .cell face member connector => .cell face member (stem.append connector)
  | .append first last => .append (based stem first) (based stem last)
termination_by structural tree => tree

/-- Changing the base preserves the exact ordered cell list.

Structural induction follows the same circuit expression. Transport changes only its connector and preserves both
ordered child lists. -/
theorem based_cells {first last : Gaussian.Basic.Canonical} (stem : Geometry.Grid.Walks.Walk grid first last) (tree :
  Geometry.Grid.RowCircuitOrder.CellCircuits grid last) :
    (tree.based stem).cells = tree.cells := by
  induction tree with
  | nil => rfl
  | cell => rfl
  | append first last ihFirst ihLast => exact congrArg₂ List.append ihFirst ihLast

/-- Materializing a transported circuit expression agrees with basing its materialized walk.

The comparison retains the supplied edge and vertex banks and is proved for all starting sheets and antisymmetric edge
valuations. -/
theorem based_product {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} (stem : Geometry.Grid.Walks.Walk grid first last) (tree :
      Geometry.Grid.RowCircuitOrder.CellCircuits grid last) :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (tree.based
      stem).product (stem.based tree.product) := by
  induction tree with
  | nil =>
      simp only [based, Geometry.Grid.RowCircuitOrder.CellCircuits.product, Geometry.Grid.Walks.Walk.based,
        Geometry.Grid.Walks.Walk.append]
      exact (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.retrace reference
        stem).symm
  | cell cell member connector =>
      apply RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq
      simp only [based, Geometry.Grid.RowCircuitOrder.CellCircuits.product, Geometry.Grid.Walks.Walk.based,
        Polynomial.Geometry.Grid.Walks.Walk.reverse_append,
        Polynomial.Geometry.Grid.Walks.Walk.append_assoc, -eq_self]
      rfl
  | append first last ihFirst ihLast =>
      simp only [based, Geometry.Grid.RowCircuitOrder.CellCircuits.product]
      exact (ihFirst.append ihLast).trans
        (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.based_append reference stem
        first.product last.product)

end CellCircuits

namespace RowCircuits

variable (band : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial :=
  polynomial) (ambient := ambient)))
  (member : band ∈ grid.yIntervals)

/-- Read the increasing walk along the retained band's lower grid line.

The band retains its lower-line membership certificate. The supplied increasing walk supplies its original horizontal
intervals and endpoints. -/
@[expose] def bottom {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals
  start finish) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point finish band.lower.coordinate) :=
  Geometry.Grid.Walks.Walk.horizontalIncreasing band.lower (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
    grid.horizontal_ordered member).1 walk

/-- Read the increasing walk along the retained band's upper grid line.

The band retains its upper-line membership certificate. The supplied increasing walk supplies the same original
horizontal intervals and endpoints. -/
@[expose] def top {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals
  start finish) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point start band.upper.coordinate)
      (Gaussian.Components.Basic.point finish band.upper.coordinate) :=
  Geometry.Grid.Walks.Walk.horizontalIncreasing band.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
    grid.horizontal_ordered member).2 walk

/-- Form the oriented strip boundary from its bottom and top walks and the supplied side edges.

The lower increasing walk, supplied right side, reversed upper walk and supplied left side retain their original
traversal order and endpoints. -/
@[expose] def boundary {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals
  start finish)
    (left : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point start band.upper.coordinate))
    (right : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point finish band.lower.coordinate)
      (Gaussian.Components.Basic.point finish band.upper.coordinate)) :
    Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point start band.lower.coordinate) :=
  Geometry.Grid.Walks.Walk.rectangle (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band member walk) (.cons right
    (.nil _)) (Geometry.Grid.RowCircuitOrder.RowCircuits.top band member walk) (.cons left (.nil _))

/-- Form row circuits in the reversed retained axis order.

The tail is transported to the current base before the current cell runs.
The construction keeps every interval and its original grid membership. -/
@[expose] def ofWalk : {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk
  grid.xIntervals start finish) →
    Geometry.Grid.RowCircuitOrder.CellCircuits grid (Gaussian.Components.Basic.point start band.lower.coordinate)
  | _, _, .nil start => .nil (Gaussian.Components.Basic.point start band.lower.coordinate)
  | _, _, .cons interval adjacent tail =>
      let cell := Geometry.Grid.ClearGrid.Cell.mk interval band
      let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
      let stem : Geometry.Grid.Walks.Walk grid cell.box.anchor (Gaussian.Components.Basic.point
        interval.upper.coordinate band.lower.coordinate) :=
        .cons (cell.bottomSide cellMember) (.nil _)
      .append ((Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk tail).based stem) (.cell cell
        cellMember (.nil cell.box.anchor))

/-- The row circuit list visits the original adjacent cells in reverse axis order.

The deterministic circuit construction places the transported suffix before its current leaf. Structural reversal and
mapping preserve those same interval occurrences. -/
theorem ofWalk_cells : {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk
  grid.xIntervals start finish) →
    (Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member walk).cells = walk.edges.reverse.map (fun interval =>
      Geometry.Grid.ClearGrid.Cell.mk interval band)
  | _, _, .nil _ => rfl
  | _, _, .cons interval adjacent tail => by
      rw [Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk, Geometry.Grid.RowCircuitOrder.CellCircuits.cells]
      rw [Geometry.Grid.RowCircuitOrder.CellCircuits.based_cells,
        Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk_cells tail]
      simp only [Geometry.Grid.RowCircuitOrder.CellCircuits.cells, Geometry.Grid.AxisWalks.IncreasingWalk.edges,
        Reverse.reverse_cons,
        Map.map_append, List.map_cons, List.map_nil, -eq_self]
      rfl

/-- Compare the actual cell boundary with a rectangle using the supplied left edge.

The edge-bank comparison identifies the two traversals with the same endpoints and retains their sheet behavior. -/
private theorem cell_with_left {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (interval : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (adjacent : interval ∈ grid.xIntervals)
    (left : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point interval.lower.coordinate
      band.lower.coordinate) (Gaussian.Components.Basic.point interval.lower.coordinate band.upper.coordinate)) :
    let cell := Geometry.Grid.ClearGrid.Cell.mk interval band
    let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell cellMember)
      (Geometry.Grid.Walks.Walk.rectangle (.cons (cell.bottomSide cellMember) (.nil _)) (.cons (cell.rightSide
        cellMember) (.nil _))
        (.cons (.horizontal interval adjacent band.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
          grid.horizontal_ordered member).2) (.nil _))
        (.cons left (.nil _))) := by
  let cell := Geometry.Grid.ClearGrid.Cell.mk interval band
  let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
  exact (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.refl (.cons (cell.bottomSide
    cellMember)
    (.cons (cell.rightSide cellMember) (.cons (cell.topSide cellMember) (.nil _))))).append
      (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.edge reference (cell.leftSide
        cellMember) (.reverse left))

/-- The ordered row circuits agree with the supplied strip boundary.

The comparison fixes every intermediate sheet and cancels the retained shared
sides and connectors. A single cell need not return to its initial root. -/
theorem comparison {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    (left : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point start band.upper.coordinate)) →
    (right : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point finish band.lower.coordinate)
      (Gaussian.Components.Basic.point finish band.upper.coordinate)) →
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      (Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member walk).product
      (Geometry.Grid.RowCircuitOrder.RowCircuits.boundary band member walk left right)
  | _, _, .nil _, left, right => by
      simp only [Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk, Geometry.Grid.RowCircuitOrder.CellCircuits.product,
        Geometry.Grid.RowCircuitOrder.RowCircuits.boundary, Geometry.Grid.RowCircuitOrder.RowCircuits.bottom,
        Geometry.Grid.RowCircuitOrder.RowCircuits.top, Geometry.Grid.Walks.Walk.horizontalIncreasing,
        Geometry.Grid.Walks.Walk.rectangle, Geometry.Grid.Walks.Walk.append, Geometry.Grid.Walks.Walk.reverse,
          Geometry.Grid.Walks.Walk.reverseOnto]
      have side := (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.edge (edges :=
        edges) (vertices := vertices) reference right left).append
        (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.refl
          ((Geometry.Grid.Walks.Walk.cons left (.nil _)).reverse))
      exact ((side.trans (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.retrace
        reference (.cons left (.nil _)))).symm)
  | _, _, .cons interval adjacent tail, left, right => by
      let cell := Geometry.Grid.ClearGrid.Cell.mk interval band
      let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
      let stem : Geometry.Grid.Walks.Walk grid cell.box.anchor (Gaussian.Components.Basic.point
        interval.upper.coordinate band.lower.coordinate) :=
        .cons (cell.bottomSide cellMember) (.nil _)
      let upper : Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point interval.lower.coordinate
        band.upper.coordinate) (Gaussian.Components.Basic.point interval.upper.coordinate band.upper.coordinate) :=
        .cons (.horizontal interval adjacent band.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
          grid.horizontal_ordered member).2) (.nil _)
      have tailComparison := Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits.comparison (edges := edges)
        (vertices := vertices)
        reference tail (cell.rightSide cellMember) right
      have based := ((Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member tail).based_product reference
        stem).trans (tailComparison.based stem)
      have head := Geometry.Grid.RowCircuitOrder.RowCircuits.cell_with_left (edges := edges) (vertices := vertices) band
        member reference interval adjacent left
      have joined := based.append head
      have sewn := RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.horizontal_sewing
        (edges := edges) (vertices := vertices) reference stem
        (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band member tail) (.cons right (.nil _))
          (Geometry.Grid.RowCircuitOrder.RowCircuits.top band member tail) upper (.cons left (.nil _))
        (.cons (cell.rightSide cellMember) (.nil _))
      apply (RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans
        (joined.trans sewn)
      simp only [Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk, Geometry.Grid.RowCircuitOrder.CellCircuits.product,
        Geometry.Grid.Walks.Walk.based, Geometry.Grid.Walks.Walk.append, Geometry.Grid.Walks.Walk.reverse,
        Geometry.Grid.Walks.Walk.reverseOnto]
      exact congrArg (fun rest => ((Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member tail).based
        stem).product.append rest)
        (Polynomial.Geometry.Grid.Walks.Walk.append_nil
          (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell cellMember))

set_option genInjectivity false in
/-- Cache the ordered circuit expression and its materialized path.

All correctness fields concern the same original axis, cell occurrences and
edge bank. The cached product and outer boundary retain their comparison. -/
structure Prepared {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals
  start finish)
    (left : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point start band.upper.coordinate))
    (right : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point finish band.lower.coordinate)
      (Gaussian.Components.Basic.point finish band.upper.coordinate))
    {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
      RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
      RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid) where
  /-- The retained ordered expression of based cell boundaries. -/ tree : Geometry.Grid.RowCircuitOrder.CellCircuits
    grid (Gaussian.Components.Basic.point start band.lower.coordinate)
  /-- The expression equals the deterministic row construction for the original axis walk. -/ tree_eq : tree =
    Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member walk
  /-- The cached ordered list of actual grid cells. -/ cells : List (Geometry.Grid.ClearGrid.Cell polynomial ambient)
  /-- The cached cell list is exactly the retained expression's cell list. -/ cells_eq : cells = tree.cells
  /-- The cell occurrences follow the reversed adjacent-axis order. -/ order : cells = walk.edges.reverse.map (fun
    interval => Geometry.Grid.ClearGrid.Cell.mk interval band)
  /-- The cached materialized closed walk of the circuit expression. -/ product : Geometry.Grid.Walks.Walk grid
    (Gaussian.Components.Basic.point start band.lower.coordinate) (Gaussian.Components.Basic.point start
    band.lower.coordinate)
  /-- The cached product is exactly the materialization of the retained expression. -/ product_eq : product =
    tree.product
  /-- The cached oriented outer strip boundary. -/ outer : Geometry.Grid.Walks.Walk grid
    (Gaussian.Components.Basic.point start band.lower.coordinate) (Gaussian.Components.Basic.point start
    band.lower.coordinate)
  /-- The cached outer walk equals the boundary built from the original axis and side edges. -/ outer_eq : outer =
    Geometry.Grid.RowCircuitOrder.RowCircuits.boundary band member walk left right
  /-- The retained product and outer boundary agree through the original edge and vertex banks. -/ comparison :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices product outer

constructive_injectivity Prepared

/-- Cache the row circuit expression, its exact ordered cells, materialized product and outer boundary.

The construction retains their defining equalities and builds the comparison from the original axis, edge bank and
vertex bank. -/
@[expose] def prepare {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish)
    (left : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point start band.lower.coordinate)
      (Gaussian.Components.Basic.point start band.upper.coordinate))
    (right : Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point finish band.lower.coordinate)
      (Gaussian.Components.Basic.point finish band.upper.coordinate)) :
    Geometry.Grid.RowCircuitOrder.RowCircuits.Prepared band member walk left right edges vertices :=
  let tree := Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk band member walk
  ⟨tree, rfl, tree.cells, rfl, Geometry.Grid.RowCircuitOrder.RowCircuits.ofWalk_cells band member walk, tree.product,
    rfl,
    Geometry.Grid.RowCircuitOrder.RowCircuits.boundary band member walk left right, rfl,
      Geometry.Grid.RowCircuitOrder.RowCircuits.comparison band member reference walk left right⟩

end RowCircuits
end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
