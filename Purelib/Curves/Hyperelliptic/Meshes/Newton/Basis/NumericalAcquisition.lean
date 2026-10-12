module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

public section

/-! Acquire one numerical threshold for the synchronized observation and physical owner banks. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

open Purelib.Curves
open Purelib.Riemann

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {differential : Hyperelliptic.Differentials.Basic.Differential
    genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

section RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

variable {whole :
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {selected : PuncturedGrid.Exterior.SourceCuts whole previous}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared} {index :
    Nat} {inputs : retained.Inputs index}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum)

variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
  Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCoarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {surfaceTarget : Normalization.InverseRootPolynomial.Coordinate}
  (initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests surfaceCoarse surfaceFixed
    surfaceTarget)

section SurfaceAcquisition
variable {schedules initialSurface} (acquired :
  SurfaceAcquisition schedules initialSurface)
  (vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    acquired.spatial.refined outer) → Nat)

set_option genInjectivity false in
/-- Cache the shared physical owners and their numerical floor together with the observation threshold. -/
structure NumericalAcquisition where
  /-- The computed shared physical-piece, junction and parent owner banks for the acquired geometry. -/ owners :
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    acquired.spatial.requests
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
      selected acquired.spatial.refined) vertices
  /-- The retained common face stage paying these exact shared-owner banks and the physical mesh floor. -/ face :
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage
    owners acquired.spatial.refined.index
  /-- The common numerical threshold paying both the acquired geometry and retained face owners. -/ index : Nat
  /-- The numerical threshold is exactly the maximum of the acquired geometry and face stages. -/ index_eq : index = max
    acquired.index face.stage

constructive_injectivity NumericalAcquisition

namespace NumericalAcquisition

/-- Compute and cache the original shared-owner banks and the numerical stage paying both physical and observation
requirements. -/
@[expose] def build :
  NumericalAcquisition
  acquired vertices :=
  let owners :=
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.prepareSharedOwners
    acquired.spatial.requests
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
      selected acquired.spatial.refined) vertices
  let face :=
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage.build
    owners acquired.spatial.refined.index
  ⟨owners, face, max acquired.index face.stage, rfl⟩

variable {acquired vertices} (numerical :
  NumericalAcquisition
  acquired vertices)

/-- The acquired common geometry stage is bounded by the numerical acquisition stage. -/
theorem geometry_le : acquired.index ≤ numerical.index := by
  rw [numerical.index_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- The retained face-owner stage is bounded by the numerical acquisition stage. -/
theorem face_le : numerical.face.stage ≤ numerical.index := by
  rw [numerical.index_eq]
  exact Data.Nat.Order.le_max_right _ _

/-- The acquired observation request is paid by the same numerical index as every physical owner. -/
theorem observation_le : acquired.surface.index ≤ numerical.index :=
  acquired.surface_le.trans numerical.geometry_le

/-- The actual physical mesh's numerical floor is retained in the common index. -/
theorem physical_le : acquired.spatial.refined.index ≤ numerical.index :=
  numerical.face.floor_le.trans numerical.face_le

end NumericalAcquisition
end SurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
