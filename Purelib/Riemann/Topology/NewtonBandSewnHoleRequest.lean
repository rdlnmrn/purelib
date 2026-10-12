module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandTriangleHoleRequest
public import Purelib.Riemann.Topology.NewtonBandSelectedSewing
import Purelib.Tactic.Ring
import Purelib.Riemann.Topology.NewtonSewnExcision

public section

open Purelib.Data

/-! The physical-hole cancellation is transported to the retained sewn
annular selection on the same primitive readings and selected face owner. -/
namespace Purelib.Riemann.Topology.NewtonBandSewnHoleRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation.AreaRequest
  (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus sourceMask)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Riemann.RootContinuation.NewtonBandWindowHole (fineHole)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.BandTriangleHoleRequest (triangleHoleRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {request : AreaRequest preparation
    target radius}
  {lifted : LiftedPuncturedGrid request.grid.punctured}
  {entry : AnnularEntry request.grid lifted}
  {prepared : OuterPreparation
    entry.region}
  {domains : FaceDomainBank lifted.frames
    request.grid.faces.regulars} {i j : Fin genus}

open Purelib.Curves.Hyperelliptic.Meshes.Newton in
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration in
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces in
open Purelib.Riemann in
open Purelib.Topology.Surface.Sewing in
/-- Select a stage paying physical-hole cancellation on the retained sewn annulus.

Every later cache preserves the original two primitive readings, sewn values and selected face owner. The squared error
includes both the sewing discrepancy and the outer-band and physical-hole comparison, with total allowance eighty-two
times the target. -/
@[expose] def sewnHoleRequest (comparison : AreaRequest.PairedComparison request prepared i j domains)
    (sewing : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains i j) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
        (leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
        (selected : CachedSample.FaceSelection leftSurface (sourceMask entry)),
        threshold ≤ stage →
        let value := fun edge => (⟨edgeValuation lifted.mesh left.values edge,
          CanonicalEdgeValues.edgeValuation lifted.mesh right.values edge⟩ : PrimitivePoint)
        let physical := fun sheet => Path.PairedIncrementArea.area
          ((lifted.edges.indexedEdges lifted.vertices (fineHole entry.annulus (current := lifted)).hole.boundary
            sheet).map value)
        Data.Gaussian.Norm.Basic.normSq (edgeListArea (fun vertex =>
          (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : PrimitivePoint))
          (selected.triangles.flatMap OrientedTriangle.boundary) + (physical 0 + physical 1)) ≤ 82 * target } := by
  let geometric := BandTriangleHoleRequest.triangleHoleRequest comparison sewing.leftMagnitude sewing.rightMagnitude
    floor
  let sewn := Request.build sewing target request.budget.positive floor
  refine ⟨max geometric.val sewn.index, geometric.property.1.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache left right leftSurface rightSurface selected later value physical
  have geometryBound := geometric.property.2 stage cache left right ((Nat.Order.le_max_left _ _).trans later)
  let annulus : SewnAnnulus leftSurface := ⟨entry, selected⟩
  have sewingBound := Topology.NewtonBandSelectedSewing.selected_accurate
    (rightSurface := rightSurface) left right annulus sewn ((Nat.Order.le_max_right _ _).trans later)
  let triangles := SelectedTrianglePartition.selectedFullTriangleArea left right (fun position =>
    decide ((request.grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (request.grid.bands.box
      entry.hole.index)))
  let area := edgeListArea (fun vertex =>
    (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : PrimitivePoint))
    (selected.triangles.flatMap OrientedTriangle.boundary)
  change Data.Gaussian.Norm.Basic.normSq (area - triangles) < target at sewingBound
  change Data.Gaussian.Norm.Basic.normSq (triangles + (physical 0 + physical 1)) ≤ 40 * target at geometryBound
  have estimate := (Bounds.normSq_add_le_two (area - triangles) (triangles + (physical 0 + physical 1))).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct sewingBound.le geometryBound) (by
      decide))
  rw [show area - triangles + (triangles + (physical 0 + physical 1)) =
      area + (physical 0 + physical 1) by ring1] at estimate
  exact estimate.trans_eq (by ring1)

end Purelib.Riemann.Topology.NewtonBandSewnHoleRequest
