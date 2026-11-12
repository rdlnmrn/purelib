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

open Purelib.Data.Gaussian.Components
open Purelib.RootIsolation.SquareRoot.Grid

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

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

set_option genInjectivity false in
/-- A finite ordered expression of based cell boundaries.

Every leaf retains its original cell, grid membership and literal connector.
Append nodes retain the ordered child expressions at their common base. -/
inductive CellCircuits (grid : ClearGrid polynomial ambient) : Gaussian.Basic.Canonical → Type
  /-- The empty circuit expression at a displayed base vertex. -/ | nil (base : Gaussian.Basic.Canonical) :
    RowCircuitOrder.CellCircuits grid base
  /-- One actual cell boundary, with its grid membership and connector from the common base. -/ | cell {base :
    Gaussian.Basic.Canonical} (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells)
      (stem : Walks.Walk grid base cell.box.anchor) :
        RowCircuitOrder.CellCircuits grid base
  /-- An ordered concatenation of two circuit expressions at the same base. -/ | append {base :
    Gaussian.Basic.Canonical} (first last : RowCircuitOrder.CellCircuits grid base) :
    RowCircuitOrder.CellCircuits grid base

constructive_injectivity CellCircuits

namespace CellCircuits

/-- Materialize the ordered circuit expression as a closed grid walk.

Each cell consumes its retained connector and original boundary; append nodes preserve circuit order. -/
@[expose] def product {base : Gaussian.Basic.Canonical} : CellCircuits grid base →
  Walks.Walk grid base base
  | .nil _ => .nil base
  | .cell face member stem => stem.based (CellBoundary.Cell.boundaryWalk face member)
  | .append first last => first.product.append last.product
termination_by structural tree => tree

/-- Read the cells in circuit-expression order, preserving every displayed occurrence.

Each retained leaf contributes its original cell once. Appending expressions concatenates their retained cell lists
without sorting or deduplication. -/
@[expose] def cells {base : Gaussian.Basic.Canonical} : CellCircuits grid base → List
  (ClearGrid.Cell polynomial ambient)
  | .nil _ => []
  | .cell face _ _ => [face]
  | .append first last => first.cells ++ last.cells
termination_by structural tree => tree

/-- Transport a circuit expression to a new base along a supplied grid stem.

The stem is prepended to every retained connector without changing the underlying cells. -/
@[expose] def based {first last : Gaussian.Basic.Canonical} (stem : Walks.Walk grid first last) :
  CellCircuits grid last → CellCircuits grid first
  | .nil _ => .nil first
  | .cell face member connector => .cell face member (stem.append connector)
  | .append first last => .append (based stem first) (based stem last)
termination_by structural tree => tree

/-- Changing the base preserves the exact ordered cell list.

Structural induction follows the same circuit expression. Transport changes only its connector and preserves both
ordered child lists. -/
theorem based_cells {first last : Gaussian.Basic.Canonical} (stem : Walks.Walk grid first last) (tree :
  CellCircuits grid last) :
    (tree.based stem).cells = tree.cells := by
  induction tree with
  | nil => rfl
  | cell => rfl
  | append first last ihFirst ihLast => exact congrArg₂ List.append ihFirst ihLast

/-- Materializing a transported circuit expression agrees with basing its materialized walk.

The comparison retains the supplied edge and vertex banks and is proved for all starting sheets and antisymmetric edge
valuations. -/
theorem based_product {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} (stem : Walks.Walk grid first last) (tree :
      CellCircuits grid last) :
    RootEdgeBank.ChainComparison edges vertices (tree.based
      stem).product (stem.based tree.product) := by
  induction tree with
  | nil =>
      simp only [based, product, Walks.Walk.based,
        Walks.Walk.append]
      exact (RootEdgeBank.ChainComparison.retrace reference
        stem).symm
  | cell cell member connector =>
      apply RootEdgeBank.ChainComparison.of_eq
      simp only [based, product, Walks.Walk.based,
        Walks.Walk.reverse_append,
        Walks.Walk.append_assoc, -eq_self]
      rfl
  | append first last ihFirst ihLast =>
      simp only [based, product]
      exact (ihFirst.append ihLast).trans
        (RootEdgeBank.ChainComparison.based_append reference stem
        first.product last.product)

end CellCircuits

namespace RowCircuits

variable (band : ClearGrid.Interval (ClearGrid.HorizontalLine.coordinate (polynomial :=
  polynomial) (ambient := ambient)))
  (member : band ∈ grid.yIntervals)

/-- Read the increasing walk along the retained band's lower grid line.

The band retains its lower-line membership certificate. The supplied increasing walk supplies its original horizontal
intervals and endpoints. -/
@[expose] def bottom {start finish : Fraction.Rational} (walk : AxisWalks.IncreasingWalk grid.xIntervals
  start finish) :
    Walks.Walk grid (Basic.point start band.lower.coordinate)
      (Basic.point finish band.lower.coordinate) :=
  Walks.Walk.horizontalIncreasing band.lower (ClearGrid.Interval.endpoints_mem _
    grid.horizontal_ordered member).1 walk

/-- Read the increasing walk along the retained band's upper grid line.

The band retains its upper-line membership certificate. The supplied increasing walk supplies the same original
horizontal intervals and endpoints. -/
@[expose] def top {start finish : Fraction.Rational} (walk : AxisWalks.IncreasingWalk grid.xIntervals
  start finish) :
    Walks.Walk grid (Basic.point start band.upper.coordinate)
      (Basic.point finish band.upper.coordinate) :=
  Walks.Walk.horizontalIncreasing band.upper (ClearGrid.Interval.endpoints_mem _
    grid.horizontal_ordered member).2 walk

/-- Form the oriented strip boundary from its bottom and top walks and the supplied side edges.

The lower increasing walk, supplied right side, reversed upper walk and supplied left side retain their original
traversal order and endpoints. -/
@[expose] def boundary {start finish : Fraction.Rational} (walk : AxisWalks.IncreasingWalk grid.xIntervals
  start finish)
    (left : Walks.Edge grid (Basic.point start band.lower.coordinate)
      (Basic.point start band.upper.coordinate))
    (right : Walks.Edge grid (Basic.point finish band.lower.coordinate)
      (Basic.point finish band.upper.coordinate)) :
    Walks.Walk grid (Basic.point start band.lower.coordinate)
      (Basic.point start band.lower.coordinate) :=
  Walks.Walk.rectangle (bottom band member walk) (.cons right
    (.nil _)) (top band member walk) (.cons left (.nil _))

/-- Form row circuits in the reversed retained axis order.

The tail is transported to the current base before the current cell runs.
The construction keeps every interval and its original grid membership. -/
@[expose] def ofWalk : {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk
  grid.xIntervals start finish) →
    CellCircuits grid (Basic.point start band.lower.coordinate)
  | _, _, .nil start => .nil (Basic.point start band.lower.coordinate)
  | _, _, .cons interval adjacent tail =>
      let cell := ClearGrid.Cell.mk interval band
      let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
      let stem : Walks.Walk grid cell.box.anchor (Basic.point
        interval.upper.coordinate band.lower.coordinate) :=
        .cons (cell.bottomSide cellMember) (.nil _)
      .append ((RowCircuits.ofWalk tail).based stem) (.cell cell
        cellMember (.nil cell.box.anchor))

/-- The row circuit list visits the original adjacent cells in reverse axis order.

The deterministic circuit construction places the transported suffix before its current leaf. Structural reversal and
mapping preserve those same interval occurrences. -/
theorem ofWalk_cells : {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk
  grid.xIntervals start finish) →
    (ofWalk band member walk).cells = walk.edges.reverse.map (fun interval =>
      ClearGrid.Cell.mk interval band)
  | _, _, .nil _ => rfl
  | _, _, .cons interval adjacent tail => by
      rw [ofWalk, CellCircuits.cells]
      rw [CellCircuits.based_cells,
        RowCircuits.ofWalk_cells tail]
      simp only [CellCircuits.cells, AxisWalks.IncreasingWalk.edges,
        Reverse.reverse_cons,
        Map.map_append, List.map_cons, List.map_nil, -eq_self]
      rfl

/-- Compare the actual cell boundary with a rectangle using the supplied left edge.

The edge-bank comparison identifies the two traversals with the same endpoints and retains their sheet behavior. -/
private theorem cell_with_left {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (interval : ClearGrid.Interval (ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (adjacent : interval ∈ grid.xIntervals)
    (left : Walks.Edge grid (Basic.point interval.lower.coordinate
      band.lower.coordinate) (Basic.point interval.lower.coordinate band.upper.coordinate)) :
    let cell := ClearGrid.Cell.mk interval band
    let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
    RootEdgeBank.ChainComparison edges vertices
      (CellBoundary.Cell.boundaryWalk cell cellMember)
      (Walks.Walk.rectangle (.cons (cell.bottomSide cellMember) (.nil _)) (.cons (cell.rightSide
        cellMember) (.nil _))
        (.cons (.horizontal interval adjacent band.upper (ClearGrid.Interval.endpoints_mem _
          grid.horizontal_ordered member).2) (.nil _))
        (.cons left (.nil _))) := by
  let cell := ClearGrid.Cell.mk interval band
  let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
  exact (RootEdgeBank.ChainComparison.refl (.cons (cell.bottomSide
    cellMember)
    (.cons (cell.rightSide cellMember) (.cons (cell.topSide cellMember) (.nil _))))).append
      (RootEdgeBank.ChainComparison.edge reference (cell.leftSide
        cellMember) (.reverse left))

/-- The ordered row circuits agree with the supplied strip boundary.

The comparison fixes every intermediate sheet and cancels the retained shared
sides and connectors. A single cell need not return to its initial root. -/
theorem comparison {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    (left : Walks.Edge grid (Basic.point start band.lower.coordinate)
      (Basic.point start band.upper.coordinate)) →
    (right : Walks.Edge grid (Basic.point finish band.lower.coordinate)
      (Basic.point finish band.upper.coordinate)) →
    RootEdgeBank.ChainComparison edges vertices
      (ofWalk band member walk).product
      (boundary band member walk left right)
  | _, _, .nil _, left, right => by
      simp only [ofWalk, CellCircuits.product,
        boundary, bottom,
        top, Walks.Walk.horizontalIncreasing,
        Walks.Walk.rectangle, Walks.Walk.append, Walks.Walk.reverse,
          Walks.Walk.reverseOnto]
      have side := (RootEdgeBank.ChainComparison.edge (edges :=
        edges) (vertices := vertices) reference right left).append
        (RootEdgeBank.ChainComparison.refl
          ((Walks.Walk.cons left (.nil _)).reverse))
      exact ((side.trans (RootEdgeBank.ChainComparison.retrace
        reference (.cons left (.nil _)))).symm)
  | _, _, .cons interval adjacent tail, left, right => by
      let cell := ClearGrid.Cell.mk interval band
      let cellMember := EdgeCell.cell_member (cell := cell) adjacent member
      let stem : Walks.Walk grid cell.box.anchor (Basic.point
        interval.upper.coordinate band.lower.coordinate) :=
        .cons (cell.bottomSide cellMember) (.nil _)
      let upper : Walks.Walk grid (Basic.point interval.lower.coordinate
        band.upper.coordinate) (Basic.point interval.upper.coordinate band.upper.coordinate) :=
        .cons (.horizontal interval adjacent band.upper (ClearGrid.Interval.endpoints_mem _
          grid.horizontal_ordered member).2) (.nil _)
      have tailComparison := RowCircuits.comparison (edges := edges)
        (vertices := vertices)
        reference tail (cell.rightSide cellMember) right
      have based := ((ofWalk band member tail).based_product reference
        stem).trans (tailComparison.based stem)
      have head := cell_with_left (edges := edges) (vertices := vertices) band
        member reference interval adjacent left
      have joined := based.append head
      have sewn := RootEdgeBank.ChainComparison.horizontal_sewing
        (edges := edges) (vertices := vertices) reference stem
        (bottom band member tail) (.cons right (.nil _))
          (top band member tail) upper (.cons left (.nil _))
        (.cons (cell.rightSide cellMember) (.nil _))
      apply (RootEdgeBank.ChainComparison.of_eq ?_).trans
        (joined.trans sewn)
      simp only [ofWalk, CellCircuits.product,
        Walks.Walk.based, Walks.Walk.append, Walks.Walk.reverse,
        Walks.Walk.reverseOnto]
      exact congrArg (fun rest => ((ofWalk band member tail).based
        stem).product.append rest)
        (Walks.Walk.append_nil
          (CellBoundary.Cell.boundaryWalk cell cellMember))

set_option genInjectivity false in
/-- Cache the ordered circuit expression and its materialized path.

All correctness fields concern the same original axis, cell occurrences and
edge bank. The cached product and outer boundary retain their comparison. -/
structure Prepared {start finish : Fraction.Rational} (walk : AxisWalks.IncreasingWalk grid.xIntervals
  start finish)
    (left : Walks.Edge grid (Basic.point start band.lower.coordinate)
      (Basic.point start band.upper.coordinate))
    (right : Walks.Edge grid (Basic.point finish band.lower.coordinate)
      (Basic.point finish band.upper.coordinate))
    {frames : RootFrames grid} (edges :
      RootEdgeBank frames) (vertices :
      LiftedVertices.VertexBank grid) where
  /-- The retained ordered expression of based cell boundaries. -/ tree : CellCircuits
    grid (Basic.point start band.lower.coordinate)
  /-- The expression equals the deterministic row construction for the original axis walk. -/ tree_eq : tree =
    ofWalk band member walk
  /-- The cached ordered list of actual grid cells. -/ cells : List (ClearGrid.Cell polynomial ambient)
  /-- The cached cell list is exactly the retained expression's cell list. -/ cells_eq : cells = tree.cells
  /-- The cell occurrences follow the reversed adjacent-axis order. -/ order : cells = walk.edges.reverse.map (fun
    interval => ClearGrid.Cell.mk interval band)
  /-- The cached materialized closed walk of the circuit expression. -/ product : Walks.Walk grid
    (Basic.point start band.lower.coordinate) (Basic.point start
    band.lower.coordinate)
  /-- The cached product is exactly the materialization of the retained expression. -/ product_eq : product =
    tree.product
  /-- The cached oriented outer strip boundary. -/ outer : Walks.Walk grid
    (Basic.point start band.lower.coordinate) (Basic.point start
    band.lower.coordinate)
  /-- The cached outer walk equals the boundary built from the original axis and side edges. -/ outer_eq : outer =
    boundary band member walk left right
  /-- The retained product and outer boundary agree through the original edge and vertex banks. -/ comparison :
    RootEdgeBank.ChainComparison edges vertices product outer

constructive_injectivity Prepared

/-- Cache the row circuit expression, its exact ordered cells, materialized product and outer boundary.

The construction retains their defining equalities and builds the comparison from the original axis, edge bank and
vertex bank. -/
@[expose] def prepare {frames : RootFrames grid} (edges :
  RootEdgeBank frames) (vertices :
  LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Fraction.Rational} (walk : AxisWalks.IncreasingWalk grid.xIntervals start finish)
    (left : Walks.Edge grid (Basic.point start band.lower.coordinate)
      (Basic.point start band.upper.coordinate))
    (right : Walks.Edge grid (Basic.point finish band.lower.coordinate)
      (Basic.point finish band.upper.coordinate)) :
    Prepared band member walk left right edges vertices :=
  let tree := ofWalk band member walk
  ⟨tree, rfl, tree.cells, rfl, ofWalk_cells band member walk, tree.product,
    rfl,
    boundary band member walk left right, rfl,
      comparison band member reference walk left right⟩

end RowCircuits
end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
