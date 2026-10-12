module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.Bilinear.Coverage
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Integration.Surface.Sewn.Selection.BilinearReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree

public section

/-! Existing automatic contact and magnitude acquisition pays the paired
area comparison for an actual retained face selection. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
open Purelib.Integration.Surface.Sewn.Selection
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.Bilinear
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation (Request)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {domains :
    FaceDomainBank frames faces.regulars}
  {i j : Fin genus}

namespace BilinearPreparation.Request
variable {polygon : SinglePolygon forest} {prepared :
  BilinearPreparation polygon domains i j}
  {target : Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- The actual retained triangle selection's sewn paired area agrees with the original selected local triangle sum
within the paid target.

Both differential contact and magnitude requests are discharged at the shared stage using the same cached samples. -/
theorem selected_accurate (request : BilinearPreparation.Request prepared target floor) {stage : Nat} (later :
  request.index ≤ stage)
    {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample polygon.patch left.values} {rightSurface :
      SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (sample : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface)
    {keep : Fin mesh.triangles.length → Bool} (selected : CachedSample.FaceSelection leftSurface keep) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea sample.values (selected.triangles.flatMap
      OrientedTriangle.boundary) -
      FiniteSum.Fin.sumFin (fun source => if keep source then TriangleReadings.bilinearArea left right source else 0)) <
        target := by
  have coverage : ∀ contact ∈ SewnPrimitiveContacts.sourceContacts polygon.patch.assembly, contact ∈
    prepared.contacts.entries := by
    intro contact member
    rw [prepared.contacts.entries_eq]
    exact member
  have leftAccuracy := request.left.localAccuracy_of_coverage coverage le_rfl
    (request.left_le.trans later) left leftSurface.sewn.readings
  have rightAccuracy := request.right.localAccuracy_of_coverage coverage le_rfl
    (request.right_le.trans later) right rightSurface.sewn.readings
  have bounded (source : Fin mesh.triangles.length) (which : Fin 3) :
      PrimitivePoint.Bounded
        (⟨left.values source which - left.values source 0,
          right.values source which - right.values source 0⟩ : Stokes.PrimitivePoint)
        (prepared.leftMagnitude.bound + prepared.rightMagnitude.bound) := by
    constructor
    · have scalar := (FaceMagnitudeBank.triangle_bounded prepared.leftMagnitude
        ((Data.Nat.Order.le_max_right _ _).trans (request.left.floor_le.trans (request.left_le.trans later))) left
          source which).trans
        (le_add_of_nonneg_right prepared.rightMagnitude.nonnegative)
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar
    · have scalar := (FaceMagnitudeBank.triangle_bounded prepared.rightMagnitude
        ((Data.Nat.Order.le_max_right _ _).trans (request.right.floor_le.trans (request.right_le.trans later))) right
          source which).trans
        (le_add_of_nonneg_left prepared.leftMagnitude.nonnegative)
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar
  have estimate := BilinearReadback.paired_request_accurate selected sample request.budget leftAccuracy rightAccuracy
    (fun position => bounded (Errors.traceAt leftSurface position).source)
  change Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea sample.values (selected.triangles.flatMap
    OrientedTriangle.boundary) -
    FiniteSum.Fin.sumFin (fun position => if keep (Errors.traceAt leftSurface position).source then
      TriangleReadings.bilinearArea left right (Errors.traceAt leftSurface position).source else 0)) < target
        at estimate
  rw [Coverage.source_sum polygon leftSurface
    (fun source => if keep source then TriangleReadings.bilinearArea left right source else 0)] at estimate
  exact estimate

end BilinearPreparation.Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest
