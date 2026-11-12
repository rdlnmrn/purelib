module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
public import Purelib.Topology.Surface.Sewing.CutPhysicalCycles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PhysicalCycles
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

/-! # Full physical-boundary loops of a retained closed-row basis reduction

The actual source word and every retained corrected basis word are closed.
Their computed coefficient subtraction has zero projected boundary, but it
need not vanish on one-sided columns. Original physicalCycles constructs
its complete hole/exterior loop multiples on one SAME boundary cache.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Algebra.FiniteSum.Fin
  (sumFin sumFin_congr sumFin_mul_right sumFin_mul_left sumFin_add sumFin_swap sumFin_zero)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)
open Purelib.Topology.Surface.Word

local notation "vget" => Purelib.Data.Vector.get

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : PeriodPrograms.Prepared paired} {cut : CutBank prepared}
    {word : List (OrientedEdge lifted.vertices.count)} {row : ClosedCoordinates word cut.integral}
    (coordinates : SpanningRows.BasisCoordinates cut row)

/-- The complete physical remainder of an actual closed word has zero boundary at each original lifted vertex.

Closure is proved for the GIVEN source word. The retained basis rows have
their own actual original closures; subtracting their computed integer
combination preserves the full physical row, including one-sided columns.
-/
theorem physical_boundary_zero {anchor : Fin lifted.vertices.count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor)
    (vertex : Fin lifted.vertices.count) :
    sumFin (fun column => vget coordinates.physical column *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish
        (VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)) vertex) = 0 := by
  let boundary := fun column => PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish
    (VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column)) vertex
  have sourceZero : sumFin (fun column => row.coordinates.totals column * boundary column) = 0 :=
    row.coordinates.boundary_zero (row.route.endpoints closed) vertex
  have aZero (index : Fin genus) :
      sumFin (fun column => (cut.rows.get index).a.coordinates.totals column * boundary column) = 0 :=
    (cut.rows.get index).a.coordinates.boundary_zero
      ((cut.rows.get index).a.route.endpoints (prepared.aWord_closed index)) vertex
  have bZero (index : Fin genus) :
      sumFin (fun column => (cut.rows.get index).b.coordinates.totals column * boundary column) = 0 :=
    (cut.rows.get index).b.coordinates.boundary_zero
      ((cut.rows.get index).b.route.endpoints (prepared.bWord_closed index)) vertex
  have evaluated : sumFin (fun column => row.coordinates.totals column * boundary column) =
      sumFin (fun index : Fin genus =>
        vget coordinates.a index * sumFin (fun column =>
          (cut.rows.get index).a.coordinates.totals column * boundary column) +
        vget coordinates.b index * sumFin (fun column =>
          (cut.rows.get index).b.coordinates.totals column * boundary column)) +
      sumFin (fun column => vget coordinates.physical column * boundary column) := by
    calc
      _ = sumFin (fun column => sumFin (fun index : Fin genus =>
          (vget coordinates.a index * (cut.rows.get index).a.coordinates.totals column +
            vget coordinates.b index * (cut.rows.get index).b.coordinates.totals column) * boundary column) +
          vget coordinates.physical column * boundary column) := by
        apply sumFin_congr
        intro column
        rw [coordinates.equation column, add_mul, sumFin_mul_right]
      _ = _ := by
        rw [sumFin_add, sumFin_swap]
        apply congrArg (· + sumFin (fun column => vget coordinates.physical column * boundary column))
        apply sumFin_congr
        intro index
        have distribute := sumFin_congr (fun column =>
          (show (vget coordinates.a index * (cut.rows.get index).a.coordinates.totals column +
              vget coordinates.b index * (cut.rows.get index).b.coordinates.totals column) * boundary column =
            vget coordinates.a index * ((cut.rows.get index).a.coordinates.totals column * boundary column) +
              vget coordinates.b index * ((cut.rows.get index).b.coordinates.totals column * boundary column)
            from by ring1))
        exact distribute.trans ((sumFin_add _ _).trans
          (congrArg₂ (· + ·) (sumFin_mul_left _ _) (sumFin_mul_left _ _)))
  have basisZero : sumFin (fun index : Fin genus =>
      vget coordinates.a index * sumFin (fun column =>
        (cut.rows.get index).a.coordinates.totals column * boundary column) +
      vget coordinates.b index * sumFin (fun column =>
        (cut.rows.get index).b.coordinates.totals column * boundary column)) = 0 := by
    apply (sumFin_congr ?_).trans sumFin_zero
    intro index
    rw [aZero index, bZero index, mul_zero, mul_zero, zero_add]
  rw [sourceZero, basisZero, zero_add] at evaluated
  exact evaluated.symm

/-- Construct the full original boundary-loop multiples of the actual closed-row physical remainder.

The GIVEN boundary cache must be the actual original boundaryComponents
run. Its whole factory derives the cut-edge matching internally. No row,
root, basis, boundary or word preparation is repeated by this operation.
-/
def physicalLoops {anchor : Fin lifted.vertices.count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor)
    (boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces))
    (factory : boundary = lifted.boundaryComponents) :
    PhysicalCycleCoordinates.Data boundary
      (fun column => VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column)) (vget coordinates.physical) := by
  have matching : ∀ edge, edge ∈ lifted.cutBoundaryPairs.boundary.map
      (VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
      edge ∈ boundary.cycles.flatten :=
    Eq.mpr (congrArg (fun value : BoundaryCycleDecomposition
      (triangleEdgeOccurrences lifted.mesh.triangulation.faces) => ∀ edge,
      edge ∈ lifted.cutBoundaryPairs.boundary.map
        (VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
        edge ∈ value.cycles.flatten) factory) lifted.cut_boundary_iff_boundaryComponents
  exact CutPhysicalCycles.ProjectedEdgePairing.physicalCycles
    (source := lifted.cutPolygon.patch.cut.count) (target := lifted.vertices.count)
    (labels := lifted.cutPolygon.patch.cut.vertexLabels)
    (occurrences := triangleEdgeOccurrences lifted.mesh.triangulation.faces)
    lifted.cutBoundaryPairs (Purelib.Riemann.cut_unique (lifted := lifted)) boundary matching
    (vget coordinates.physical) coordinates.physical_paired_zero (coordinates.physical_boundary_zero closed)

/-- Every retained physical remainder loop belongs to the original complete ordered hole/exterior boundary list. -/
theorem physicalLoops_words_eq {anchor : Fin lifted.vertices.count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor)
    (boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces))
    (factory : boundary = lifted.boundaryComponents) :
    (coordinates.physicalLoops closed boundary factory).rows.map Prod.snd = lifted.boundaryLoops :=
  (coordinates.physicalLoops closed boundary factory).words_eq.trans (congrArg (fun value : BoundaryCycleDecomposition
    (triangleEdgeOccurrences lifted.mesh.triangulation.faces) => value.cycles) factory)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

end
