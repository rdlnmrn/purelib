module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh

open Purelib.Curves

open Purelib.Riemann

public section

/-! Acquire one physical mesh whose depth pays all retained parent requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

section RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

variable {whole :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {selected : SourceCuts whole previous}
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

namespace SpatialAcquisition.RequestedSurfaceRuns

/-- Certify that the retained refined surface is exactly the original request advanced to the selected common depth. -/
@[expose] def MeshReadback (depths :
  RunDepthSynchronization.CommonBasisPreparation.ParentRunSchedules.DepthStage
  schedules request.depth)
    (refined : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts
        sheet coarseDepth) fixed meshTarget) : Prop :=
  refined = request.atDepth depths.depth depths.floor_le

/-- Transport the original computed occurrence schedules across the exact refined-mesh equality. -/
@[expose] def RefinedSchedules (depths :
  RunDepthSynchronization.CommonBasisPreparation.ParentRunSchedules.DepthStage
  schedules request.depth)
    {refined : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts
        sheet coarseDepth) fixed meshTarget}
    (equal : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition.RequestedSurfaceRuns.MeshReadback
      schedules depths refined) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules selected
      refined retained inputs requested minimum :=
  Eq.mp (congrArg (fun meshRequest =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules selected
    meshRequest retained inputs requested minimum) equal.symm)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth schedules
      depths.depth depths.floor_le)

/-- Certify that the retained refined schedules are exactly the transport of the original request vector. -/
@[expose] def SchedulesReadback (depths :
  RunDepthSynchronization.CommonBasisPreparation.ParentRunSchedules.DepthStage
  schedules request.depth)
    {refined : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts
        sheet coarseDepth) fixed meshTarget}
    (equal : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition.RequestedSurfaceRuns.MeshReadback
      schedules depths refined)
    (requests : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
      selected refined retained inputs requested minimum) : Prop :=
  requests = Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition.RequestedSurfaceRuns.RefinedSchedules
    schedules depths equal

end SpatialAcquisition.RequestedSurfaceRuns

set_option genInjectivity false in
/-- The refined surface and transported parent requests are retained together.
Its depth selection includes the original surface's already certified depth. -/
structure SpatialAcquisition where
  /-- The computed common depth paying the original surface and every retained run request. -/ depths :
    RunDepthSynchronization.CommonBasisPreparation.ParentRunSchedules.DepthStage
    schedules request.depth
  /-- The actual original surface request refined to the common depth. -/ refined :
    Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget
  /-- The refined mesh is exactly the depth refinement of the original request. -/ refined_eq :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition.RequestedSurfaceRuns.MeshReadback schedules
    depths refined
  /-- The original occurrence requests transported to the exact refined mesh capacities. -/ requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules selected
    refined retained inputs requested minimum
  /-- The retained requests equal the specified transport of the original schedules. -/ requests_eq :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition.RequestedSurfaceRuns.SchedulesReadback
    schedules depths refined_eq requests

constructive_injectivity SpatialAcquisition

namespace SpatialAcquisition.RequestedSurfaceRuns

/-- Select a common physical depth, refine the original surface and retain its transported occurrence requests.

Only the physical depth changes; source thresholds, original request calculations and source magnitudes remain those of
the retained schedules. -/
@[expose] def acquireSpatial :
  SpatialAcquisition schedules
  :=
  let depths :=
    RunDepthSynchronization.CommonBasisPreparation.ParentRunSchedules.DepthStage.build
    schedules request.depth
  let refined := request.atDepth depths.depth depths.floor_le
  ⟨depths, refined, rfl,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth schedules
    depths.depth depths.floor_le, rfl⟩

end SpatialAcquisition.RequestedSurfaceRuns

namespace SpatialAcquisition
variable {schedules} (acquired :
  SpatialAcquisition
  schedules)

/-- The acquired refined surface has exactly the selected common depth. -/
theorem mesh_depth : acquired.refined.depth = acquired.depths.depth :=
  congrArg Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.depth acquired.refined_eq

/-- The refined surface preserves the original numerical stage requirement. -/
theorem surface_index_le : request.index ≤ acquired.refined.index :=
  (request.atDepth_index_ge acquired.depths.depth acquired.depths.floor_le).trans_eq
    (congrArg Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.index acquired.refined_eq).symm

/-- Spatial acquisition preserves every original occurrence request depth. -/
theorem request_depth (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).depth = (schedules.get outer).depth := by
  rcases acquired with ⟨depths, refined, equal, requests, readback⟩
  cases equal
  cases readback
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_depth
    schedules depths.depth depths.floor_le outer

/-- Spatial acquisition preserves every original occurrence source-stage threshold. -/
theorem sourceIndex_readback (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).sourceIndex = (schedules.get outer).sourceIndex := by
  rcases acquired with ⟨depths, refined, equal, requests, readback⟩
  cases equal
  cases readback
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_sourceIndex
    schedules depths.depth depths.floor_le outer

/-- Spatial acquisition preserves every original occurrence source magnitude. -/
theorem magnitude_readback (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).magnitude = (schedules.get outer).magnitude := by
  rcases acquired with ⟨depths, refined, equal, requests, readback⟩
  cases equal
  cases readback
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_magnitude
    schedules depths.depth depths.floor_le outer

/-- The actual later physical mesh meets every retained source-run width cap. -/
theorem physical_depth_paid (outer : Fin prepared.occurrences.length) :
    (acquired.requests.get outer).depth ≤
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
        acquired.refined).depth :=
  (acquired.request_depth outer).le.trans ((acquired.depths.depth_le outer).trans_eq
    (acquired.mesh_depth.symm.trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRefinement.RequestedOccurrenceRuns.mesh_depth
        outer selected acquired.refined).symm))

end SpatialAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
