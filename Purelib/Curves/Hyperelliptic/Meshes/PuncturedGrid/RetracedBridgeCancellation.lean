module
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.CellularHomology
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Riemann.Topology.PreparedCycleModels
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.Ring
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Data.List.Append

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Paths

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes

@[expose] public section

/-!
# A root-coherent connector-only bridge has zero edge chain

The legacy B geometry consists of a connector and its reverse. If the return
starts at the actual transported root, its lifted edge word is literally
the reversed forward word with every orientation reversed. Construct an
empty-boundary cancellation certificate and prove zero against every
antisymmetric edge value, not merely a globally exact vertex primitive.

This diagnoses the geometric issue independently of endpoint-box tests. It
does not identify an independently seeded legacy period name with this
root-coherent lift: that analytic comparison remains a separate obligation.
Actual branch-boundary loops in the newer owner-closed B tour are not present
in the connector-only word below and cannot be discarded by this theorem.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.PolygonStokes

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge pairedEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Explicit incidence pairing, with no boundary left after the retrace. -/
theorem retrace_reordering {count : Nat} : (word : List (Stokes.OrientedEdge count)) →
    Stokes.EdgeReordering (word ++ word.reverse.map OrientedEdge.reverse) (Stokes.pairedEdgeOccurrences word)
  | [] => .nil
  | edge :: tail => by
      simp only [Data.List.Reverse.reverse_cons, Data.List.Map.map_append, List.map_cons, List.map_nil,
        List.cons_append, Stokes.pairedEdgeOccurrences]
      apply EdgeReordering.cons edge
      have moved := EdgeReordering.symm (EdgeReordering.move_head edge.reverse (tail ++ tail.reverse.map
        OrientedEdge.reverse) [])
      have paired := EdgeReordering.cons edge.reverse
        (retrace_reordering
        tail)
      apply EdgeReordering.trans ?_ paired
      simpa only [Data.List.Append.append_nil, Data.List.Append.append_assoc] using moved

/-- Pair each original oriented edge with its reversed return occurrence, retaining an empty boundary. -/
def cancelRetrace {count : Nat} (word : List (Stokes.OrientedEdge count)) :
    Topology.Mesh.EdgeCancellation (word ++ word.reverse.map OrientedEdge.reverse) where
  boundary := []
  internalEdges := word
  incidence := retrace_reordering
    word
  boundary_subset := fun _ member => (List.not_mem_nil member).elim
  noReversePair := .nil

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.PolygonStokes

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.RootEdgeBank

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)
open _root_.Purelib.Topology.Mesh (EdgeCancellation)
open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge pairedEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

/-- Construct empty-boundary incidence cancellation for a walk followed by its root-coherent reversal.

The retained root edge bank, vertex bank and reference loops identify the actual transported return sheet; the original
forward edge occurrences are the internal pairs. -/
def retraceCancellation (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) (sheet : Fin 2) :
    Topology.Mesh.EdgeCancellation (edges.indexedEdges vertices (walk.append walk.reverse) sheet) where
  boundary := []
  internalEdges := edges.indexedEdges vertices walk sheet
  incidence := by
    rw [edges.indexedEdges_append, edges.indexedEdges_reverse vertices reference]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.PolygonStokes.retrace_reordering _
  boundary_subset := fun _ member => (List.not_mem_nil member).elim
  noReversePair := .nil

/-- The retained cancellation certificate for the root-coherent retrace has empty boundary. -/
theorem retraceCancellation_boundary (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank
  grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) (sheet : Fin 2) :
    (retraceCancellation edges
      vertices reference walk sheet).boundary = [] := rfl

/-- For antisymmetric edge values, the reversed and orientation-reversed word has the negative original finite sum. -/
private theorem reverse_values {count : Nat} (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical)
    (opposite : ∀ edge, value edge.reverse = -value edge) : (word : List (Stokes.OrientedEdge count)) →
      CellBoundary.sumValues value (word.reverse.map OrientedEdge.reverse) = -CellBoundary.sumValues value word
  | [] => by change (0 : Data.Gaussian.Basic.Canonical) = -0; ring1
  | edge :: tail => by
      rw [Data.List.Reverse.reverse_cons, Data.List.Map.map_append, CellBoundary.sumValues_append,
        reverse_values value
        opposite tail]
      change -CellBoundary.sumValues value tail + (value edge.reverse + 0) = -(value edge + CellBoundary.sumValues value
        tail)
      rw [opposite]
      ring1

/-- No exactness or face-zero hypothesis on the edge values is used. In particular this is not the erroneous telescoping
of a nontrivial period on the uncut surface's global vertex labels. -/
theorem retrace_values_zero (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (opposite : ∀ edge, value edge.reverse
      = -value edge)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) (sheet : Fin 2) :
    CellBoundary.sumValues value (edges.indexedEdges vertices (walk.append walk.reverse) sheet) = 0 := by
  rw [edges.indexedEdges_append, edges.indexedEdges_reverse vertices reference, CellBoundary.sumValues_append,
    reverse_values value opposite]
  ring1

/-- In particular, no additive oriented-edge pairing can assign the unit intersection required of a symplectic B cycle
to this actual lift. This is a geometric obstruction, not a claim about independently seeded integrals. -/
theorem retrace_no_unit_pairing (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (opposite : ∀ edge, value edge.reverse
      = -value edge)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) (sheet : Fin 2)
    (unit : CellBoundary.sumValues value (edges.indexedEdges vertices (walk.append walk.reverse) sheet) = 1) : False :=
  (by decide : (0 : Data.Gaussian.Basic.Canonical) ≠ 1)
    ((retrace_values_zero edges
    vertices reference value opposite walk sheet).symm.trans unit)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.RootEdgeBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.PreparedDoublePath

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Riemann.Topology.PreparedCycleModels (PreparedDoublePath)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

/-- Apply the actual-root cancellation to the stored legacy connector on a shared grid. This uses its full split path,
not just its endpoints, labels, or number of cells. No new integration bank is prepared. -/
def gridRetraceCancellation {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PreparedCycleModels.PreparedDoublePath curve) {ambient : Rational.Box} (grid :
      Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient)
    (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid data.basePath) {frames :
      RootIsolation.SquareRoot.Grid.RootFrames grid}
    (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (sheet : Fin 2) :
    let walk := Walks.splitPath grid data.basePath onGrid
    Topology.Mesh.EdgeCancellation (edges.indexedEdges vertices (walk.append walk.reverse) sheet) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.RootEdgeBank.retraceCancellation edges vertices
    reference (Walks.splitPath grid data.basePath onGrid) sheet

/-- The formal standard A/B trace pairing cannot be transported by an additive oriented-edge map onto the root-coherent
legacy connector retrace. This discharges a concrete impossibility in the requested standard-basis interface:
construction tags alone do not identify its geometric cycles. No equivalence with the legacy numerical period name is
assumed or refuted by this theorem. -/
theorem gridRetrace_not_standardB {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PreparedCycleModels.PreparedDoublePath curve) {ambient : Rational.Box} (grid :
      Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient)
    (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid data.basePath) {frames :
      RootIsolation.SquareRoot.Grid.RootFrames grid}
    (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (sheet : Fin 2) (basis : BranchCutLifts.SymplecticBasis curve) (index : Fin genus)
    (pairing : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (opposite : ∀ edge, pairing edge.reverse = -pairing edge)
    (realizes : CellBoundary.sumValues pairing (edges.indexedEdges vertices
      ((Walks.splitPath grid data.basePath onGrid).append (Walks.splitPath grid data.basePath onGrid).reverse) sheet) =
        (CellularHomology.intersection (basis.aTrace index) (basis.bTrace index) : Data.Gaussian.Basic.Canonical)) :
          False := by
  have unit : CellularHomology.intersection (basis.aTrace index) (basis.bTrace index) = 1 :=
    (basis.a_b index index).trans (if_pos rfl)
  rw [unit] at realizes
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.RootEdgeBank.retrace_no_unit_pairing edges
    vertices reference pairing opposite (Walks.splitPath grid data.basePath onGrid) sheet realizes

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetracedBridgeCancellation.PreparedDoublePath
