module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-! Preserve the computed common physical depth while acquiring later source inputs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceDepthReadback

open Purelib.Data

open Purelib.Riemann.Normalization

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

namespace RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition (build)

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

open Purelib.Riemann.RootContinuation.NewtonProtectedObservations
variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {partitions :
  Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCoarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {surfaceTarget : Normalization.InverseRootPolynomial.Coordinate}
  (initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests surfaceCoarse surfaceFixed
    surfaceTarget)

namespace SurfaceAcquisition

/-- Updating numerical source inputs cannot change the computed physical depth when parent requests are retained. -/
theorem build_depth_readback {laterIndex : Nat} {laterInputs : retained.Inputs laterIndex}
    (laterSchedules :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules selected
      request retained laterInputs requested minimum)
    (same : ∀ outer, (laterSchedules.get outer).depth = (schedules.get outer).depth) :
    (build laterSchedules initialSurface).spatial.depths.depth = (build schedules initialSurface).spatial.depths.depth
      := by
  change max (max request.depth initialSurface.depth)
      ((Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition.RequestedSurfaceRuns.observationSchedules laterSchedules
        initialSurface).maximum (fun _ entry => entry.depth)) =
    max (max request.depth initialSurface.depth)
      ((Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition.RequestedSurfaceRuns.observationSchedules schedules
        initialSurface).maximum (fun _ entry => entry.depth))
  apply congrArg (Nat.max (max request.depth initialSurface.depth))
  apply Data.Vector.DependentVector.maximum_eq
  intro outer
  exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_depth
    laterSchedules _ (Nat.Order.le_max_left ..) outer).trans
    ((same outer).trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_depth
      schedules _ (Nat.Order.le_max_left ..) outer).symm)

variable {schedules} (sourceStage :
  PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules.SourceStage
  schedules) {laterIndex : Nat}
  {later : sourceStage.stage ≤ laterIndex} (source :
    CommonBasisPreparation.ParentRunSchedules.SourceStage.Acquisition
    sourceStage later)

/-- The acquired source bank reuses the precomputed common physical depth. -/
theorem acquired_source_depth :
    (build source.requests initialSurface).spatial.depths.depth = (build schedules initialSurface).spatial.depths.depth
      :=
  Hyperelliptic.Meshes.Newton.Basis.SourceDepthReadback.RequestedSurfaceRuns.SurfaceAcquisition.build_depth_readback
    schedules initialSurface source.requests
    (CommonBasisPreparation.ParentRunSchedules.SourceStage.Acquisition.depth_readback
    source)

/-- The original observation refinement also remains at that same computed depth. -/
theorem acquired_source_surface_depth :
    (build source.requests initialSurface).surface.depth = (build schedules initialSurface).surface.depth :=
  Hyperelliptic.Meshes.Newton.Basis.SourceDepthReadback.RequestedSurfaceRuns.SurfaceAcquisition.acquired_source_depth
    initialSurface sourceStage source

end SurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceDepthReadback
