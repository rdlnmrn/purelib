module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary
import Purelib.Data.Gaussian.Field

@[expose] public section

/-! Exact readback from the complete surface's outer corner polygons to
the shared period-triangle cache, with the conjugate energy component retained. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests (GlobalEnergyRequest)
open Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (cornerBoundary)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy.SynchronizedSurfaceRequests.GlobalEnergyRequest
  (energy_lower_after_contacts)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (pairedCentered physicalCentered)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint triangleWedgeArea)
open _root_.Purelib.Data.Gaussian.Basic (conj)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Periods in
/-- Sum of cached four-corner areas over regular faces and sheets.

Reads every corner from the same coefficient-combined numerical cache in the retained rectangle order. -/
def cachedCornerBoundary (cache : Numerics domains stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus) : Gaussian
  :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet : Fin 2 =>
    BilinearGridBoundary.cornerArea
      (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 0)
      (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 1)
      (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 2)
      (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 3)))

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- The retained corner boundary equals its cached readback.

Uses the exact outer-corner identities pointwise in both finite indices, preserving the actual face assemblies. -/
theorem cornerBoundary_cached {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters) :
    cornerBoundary faces = cachedCornerBoundary cache coefficients := by
  unfold cornerBoundary cachedCornerBoundary
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  let face := (faces.get sheet).get position
  change BilinearGridBoundary.cornerArea
    (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false false)
      (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true false)
    (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true true)
      (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false true) = _
  rw [Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
    Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
    Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
    Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached]
  rfl

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {mesh : LiftedMesh vertices edges grid.faces}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Basis-indexed triangle readings for one cache and lifted mesh.

The dependent bank keeps each differential cache and the original mesh triangle owner. -/
def EnergyTriangleReadings (cache : Numerics domains stage) (mesh : LiftedMesh vertices edges grid.faces) :=
  Vector.DependentVector (fun basis : Fin genus => Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
    (cache.get basis) mesh)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
/-- Coefficient-combined primitive pair at a retained triangle corner.

Keeps the conjugated coefficient/value sum separate from the ordinary coefficient/value sum. -/
def triangleValue (readings : EnergyTriangleReadings cache mesh) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (triangle : Fin mesh.triangles.length) (corner : Fin 3) : PrimitivePoint :=
  ⟨sumFin (fun basis => Data.Gaussian.Basic.conj (coefficients basis) * Data.Gaussian.Basic.conj ((readings.get
    basis).values
    triangle corner)),
    FiniteSum.Fin.sumFin (fun basis => coefficients basis * (readings.get basis).values triangle corner)⟩

open Purelib.LinearAlgebra.Gaussian in
/-- Oriented wedge area of a retained triangle's three primitive values.

Uses the coefficient-combined values in their original corner order. -/
def triangleEnergy (readings : EnergyTriangleReadings cache mesh) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (triangle : Fin mesh.triangles.length) : Gaussian :=
  triangleWedgeArea (triangleValue readings coefficients triangle 0)
    (triangleValue readings coefficients triangle 1) (triangleValue readings coefficients triangle 2)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Topology.Surface in
/-- A retained triangle corner reads the corresponding cached face corner.

Transports each basis reading through the exact triangle source identity, preserving the conjugated and ordinary
components separately. -/
theorem triangleValue_readback (readings : EnergyTriangleReadings cache mesh)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (upper : Bool) (corner : Fin 3) :
    triangleValue readings coefficients (mesh.triangleIndex position sheet upper) corner =
      Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet
        (Sewing.SewnPrimitiveFaces.corner (Meshes.PuncturedGrid.Face.Corners.FaceCorners.triangle upper) corner) := by
  apply congrArg₂ PrimitivePoint.mk
  · apply FiniteSum.Fin.sumFin_congr
    intro basis
    rw [(readings.get basis).values_eq]
    simp only [Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners.triangleValues, Vector.Basic.vectorOfFn_apply]
    rfl
  · apply FiniteSum.Fin.sumFin_congr
    intro basis
    rw [(readings.get basis).values_eq]
    simp only [Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners.triangleValues, Vector.Basic.vectorOfFn_apply]
    rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- The two triangles of one sheet face sum to its cached corner area.

Uses the exact corner readbacks and the rectangle's oriented two-triangle decomposition. -/
theorem triangleEnergy_pair (readings : EnergyTriangleReadings cache mesh)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) :
    triangleEnergy readings coefficients (mesh.triangleIndex position sheet false) +
      triangleEnergy readings coefficients (mesh.triangleIndex position sheet true) =
      BilinearGridBoundary.cornerArea
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 0)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 1)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 2)
        (Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position sheet 3) := by
  unfold triangleEnergy
  rw [triangleValue_readback, triangleValue_readback, triangleValue_readback,
    triangleValue_readback, triangleValue_readback, triangleValue_readback]
  exact (BilinearGridBoundary.cornerArea_eq_differences _ _ _ _).symm

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- The retained corner boundary is the sum of all triangle energies.

Reindexes the actual lifted mesh triangles by regular face and sheet, then applies each exact paired-triangle identity.
-/
theorem cornerBoundary_triangles {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    (readings : EnergyTriangleReadings cache mesh) :
    cornerBoundary faces = FiniteSum.Fin.sumFin (triangleEnergy readings coefficients) := by
  rw [cornerBoundary_cached, Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum mesh]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  exact (triangleEnergy_pair readings position sheet).symm

section PaidEnergy

variable {depth : Nat}
  {requests : SynchronizedSurfaceRequests (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {ownershipAllowance exteriorAllowance faceAllowance contactAllowance : Rational}

open Purelib in
open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Readings in
open Purelib.Riemann.Topology in
/-- Retain the global energy lower bound on the shared triangle readings.

Replaces the corner boundary by its exact triangle sum after paying the contact allowance, keeping the physical centered
contribution and all original deductions. -/
theorem shared_triangle_energy_lower
    (request : GlobalEnergyRequest requests ownershipAllowance exteriorAllowance faceAllowance)
    (later : request.index ≤ stage)
    (surfaceReadings : Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Topology.BranchedCover.Double.Attachment.Face)
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    {traces : PerimeterTraces requests} (samples : PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (positive : 0 < contactAllowance)
    (contacts : Data.Gaussian.Norm.Basic.normSq (pairedCentered samples) ≤
      (4 * (contactAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients))^2)
    (readings : EnergyTriangleReadings cache mesh) :
    (2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) - contactAllowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        (FiniteSum.Fin.sumFin (triangleEnergy readings coefficients) + physicalCentered samples neighbors).im / 4 := by
  rw [← cornerBoundary_triangles faces readings]
  exact energy_lower_after_contacts request later surfaceReadings observationFace faces samples neighbors positive
    contacts

end PaidEnergy

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback
