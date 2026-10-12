module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateChartAreaRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Opposite-sheet conjugate polygons on the actual edge valuation reuse
both chart requests and the retained whole-walk comparison. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PolygonRequests (PolygonRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {leftDifferential rightDifferential : Differential genus}
  {start finish : Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
    base.bank.grid start finish}

variable {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains
  rightDifferential}
  {paired : PairedWalk mesh walk} {first last :
    Fin 2} {error : Rational}
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests.PolygonRequest

/-- At the paid stage, the two actual opposite-sheet conjugate polygons differ within the original squared-area target.

Both chart transfers reuse the source observations from the same retained whole-walk conjugate comparison. -/
theorem conjugate_accurate (request : PolygonRequest leftFixed rightFixed paired first last error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (different : first ≠ last) :
    let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh
      leftReadings.values edge),
      CanonicalEdgeValues.edgeValuation mesh rightReadings.values edge⟩ : PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((edges.indexedEdges vertices walk first).map
      value) -
      PairedIncrementArea.area ((edges.indexedEdges vertices walk last).map value)) ≤ error := by
  intro value
  let oppositeComparison := request.opposite.realizeConjugate leftReadings rightReadings ((Data.Nat.Order.le_max_left _
    _).trans later) first last different
  have opposite := oppositeComparison.pay
  rw [oppositeComparison.residual_readback] at opposite
  have chartsLater := (Data.Nat.Order.le_max_right _ _).trans later
  let leftComparison := request.leftChart.realizeSupplied .conjugate leftReadings rightReadings
    ((Data.Nat.Order.le_max_left _ _).trans chartsLater) oppositeComparison.leftSources
  have left := leftComparison.pay
  rw [leftComparison.residual_readback] at left
  let rightComparison := request.rightChart.realizeSupplied .conjugate leftReadings rightReadings
    ((Data.Nat.Order.le_max_right _ _).trans chartsLater) oppositeComparison.rightSources
  have right := rightComparison.pay
  rw [rightComparison.residual_readback] at right
  let source := fun sheet => PairedIncrementArea.area ((paired.sources sheet).map (fun source =>
    (⟨Data.Gaussian.Basic.conj (SourceEdge.increment source leftReadings.values), SourceEdge.increment source
      rightReadings.values⟩ : PrimitivePoint)))
  let polygon := fun sheet => PairedIncrementArea.area ((edges.indexedEdges vertices walk sheet).map value)
  have readback (sheet : Fin 2) :
      PairedIncrementArea.area ((paired.sources sheet).map (fun source => value (source.project
        mesh.triangulation.faces))) =
        polygon sheet := by
    unfold polygon
    rw [← paired.sources_project sheet, Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (source first - PairedIncrementArea.area
    ((paired.sources first).map (fun source => value (source.project mesh.triangulation.faces)))) ≤ error / 10 at left
  rw [readback first] at left
  change Data.Gaussian.Norm.Basic.normSq (source last - PairedIncrementArea.area
    ((paired.sources last).map (fun source => value (source.project mesh.triangulation.faces)))) ≤ error / 10 at right
  rw [readback last] at right
  have reversed : Data.Gaussian.Norm.Basic.normSq (polygon first - source first) ≤ error / 10 := by
    rw [show polygon first - source first = -(source first - polygon first) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact left
  have middle : Data.Gaussian.Norm.Basic.normSq (source first - polygon last) ≤ 2 * (error / 10 + error / 10)
    :=
    (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (source first) (source last) (polygon last)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct opposite
        right) (by decide))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (polygon first) (source first) (polygon last)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct reversed
      middle) (by decide))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 10 + 2 * (error / 10 + error / 10)) = error / 10 * 10).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePolygonRequests.PolygonRequest

end
