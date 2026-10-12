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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
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
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceDepthReadback
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs

open Purelib.Curves

open Purelib.Riemann

public section

/-! Compute source and common-cover floors for the synchronized component acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

open Purelib.Data

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns

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

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (energyTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (traceFloor sourceFloor : Nat)

set_option genInjectivity false in
/-- Choose the common cover before the final source stage; retained parent depths make this order constructive. -/
structure SourceSurfaceAcquisition where
  /-- The initial synchronized physical and observation acquisition from the original schedules. -/ seed :
    SurfaceAcquisition schedules
    initialSurface
  /-- The seed is exactly the original synchronized acquisition constructor. -/ seed_eq : seed =
    SurfaceAcquisition.build schedules
    initialSurface
  /-- The reference-cover floor paying both the trace floor and the computed physical depth. -/ coverFloor : Nat
  /-- The cover floor is exactly the maximum of the trace floor and seed physical depth. -/ cover_eq : coverFloor = max
    traceFloor seed.spatial.depths.depth
  /-- The original source comparison request at the retained common-cover floor. -/ request :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis energyTarget
    coefficientTarget coverFloor sourceFloor
  /-- The common source stage paying the original occurrence schedules. -/ sourceStage :
    PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage
    schedules
  /-- The numerical input stage paying both the source comparison and occurrence requests. -/ index : Nat
  /-- The input stage is exactly the maximum of the comparison request and common source stages. -/ index_eq : index =
    max request.index sourceStage.stage
  /-- The retained common source stage is paid at the input acquisition index. -/ sourceLater : sourceStage.stage ≤
    index
  /-- The actual acquired input bank and original requests transported to those exact inputs. -/ source :
    CommonBasisPreparation.ParentRunSchedules.SourceStage.Acquisition
    sourceStage sourceLater
  /-- The synchronized physical and observation geometry using the acquired request bank. -/ geometry :
    SurfaceAcquisition source.requests
    initialSurface
  /-- Source acquisition preserves the common physical depth computed by the seed geometry. -/ depth_eq :
    geometry.spatial.depths.depth = seed.spatial.depths.depth

constructive_injectivity SourceSurfaceAcquisition

namespace SourceSurfaceAcquisition

/-- Both source and cover obligations are computed without a search or a caller depth certificate. -/
@[expose] def build (positive : 0 < energyTarget) (coefficientPositive : 0 < coefficientTarget) :
    SourceSurfaceAcquisition schedules
      initialSurface basis energyTarget coefficientTarget traceFloor sourceFloor := by
  let seed := SurfaceAcquisition.build
    schedules initialSurface
  let coverFloor := max traceFloor seed.spatial.depths.depth
  let request := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest.build retained basis
    energyTarget coefficientTarget positive coefficientPositive coverFloor sourceFloor
  let sourceStage :=
    PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage.build
    schedules
  let index := max request.index sourceStage.stage
  have sourceLater : sourceStage.stage ≤ index := Nat.Order.le_max_right _ _
  let source :=
    PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs.CommonBasisPreparation.ParentRunSchedules.SourceStage.acquire
    sourceStage sourceLater
  let geometry := SurfaceAcquisition.build
    source.requests initialSurface
  exact ⟨seed, rfl, coverFloor, rfl, request, sourceStage, index, rfl, sourceLater, source, geometry,
    Hyperelliptic.Meshes.Newton.Basis.SourceDepthReadback.RequestedSurfaceRuns.SurfaceAcquisition.acquired_source_depth
      initialSurface sourceStage source⟩

variable {schedules initialSurface basis energyTarget coefficientTarget traceFloor sourceFloor}
  (acquired :
    SourceSurfaceAcquisition
    schedules initialSurface basis energyTarget coefficientTarget traceFloor sourceFloor)

/-- Every transported source query is paid at the retained numerical input index. -/
theorem source_paid (outer : Fin prepared.occurrences.length) :
    (acquired.source.requests.get outer).sourceIndex ≤ acquired.index := acquired.source.source_paid outer

/-- The final physical mesh is covered by the source request's common reference depth. -/
theorem physical_cover_paid : acquired.geometry.spatial.depths.depth ≤ acquired.coverFloor := by
  rw [acquired.depth_eq, acquired.cover_eq]
  exact Nat.Order.le_max_right _ _

/-- The original trace allocation's floor is also included in the chosen cover. -/
theorem trace_cover_paid : traceFloor ≤ acquired.coverFloor := by
  rw [acquired.cover_eq]
  exact Nat.Order.le_max_left _ _

/-- The final input index includes the source comparison request itself. -/
theorem request_le : acquired.request.index ≤ acquired.index := by
  rw [acquired.index_eq]
  exact Nat.Order.le_max_left _ _

/-- Acquisition preserves the numerical floor from which the parent requests were computed. -/
theorem initial_index_le : index ≤ acquired.index :=
  acquired.sourceStage.index_le.trans acquired.sourceLater

/-- Geometry refinement and source acquisition preserve each retained parent depth. -/
theorem parent_depth_readback (outer : Fin prepared.occurrences.length) :
    (acquired.geometry.spatial.requests.get outer).depth = (schedules.get outer).depth :=
  (SurfaceAcquisition.request_depth
    acquired.geometry outer).trans

      (CommonBasisPreparation.ParentRunSchedules.SourceStage.Acquisition.depth_readback
      acquired.source outer)

/-- Downstream comparisons reuse the original cached source magnitude. -/
theorem parent_magnitude_readback (outer : Fin prepared.occurrences.length) :
    (acquired.geometry.spatial.requests.get outer).magnitude = (schedules.get outer).magnitude :=
  (SurfaceAcquisition.magnitude_readback
    acquired.geometry outer).trans

      (CommonBasisPreparation.ParentRunSchedules.SourceStage.Acquisition.magnitude_readback
      acquired.source outer)

end SourceSurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
