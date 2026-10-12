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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib.Curves

open Purelib.Riemann

public section

/-! Synchronize acquired common-basis physical runs with the observation surface. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

open Purelib.Data

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

namespace SurfaceAcquisition.RequestedSurfaceRuns

/-- Retain the source requests after raising the mesh floor to include observation refinement. -/
@[expose] def observationSchedules :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules selected
    (request.atDepth (max request.depth initialSurface.depth) (Nat.Order.le_max_left ..)) retained inputs requested
      minimum :=
  atDepth schedules (max request.depth initialSurface.depth) (Nat.Order.le_max_left ..)

end SurfaceAcquisition.RequestedSurfaceRuns

set_option genInjectivity false in
/-- The physical and observation meshes are acquired together at the depth required by all parent runs. -/
structure SurfaceAcquisition where
  /-- The physical spatial acquisition after including the original observation depth. -/ spatial :
    PuncturedGrid.Exterior.Basis.SpatialAcquisition
    (Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition.RequestedSurfaceRuns.observationSchedules schedules
    initialSurface)
  /-- The retained observation surface refined to the same physical depth. -/ surface :
    Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests surfaceCoarse surfaceFixed surfaceTarget
  /-- The acquired physical and observation surfaces have exactly the same depth. -/ same_depth : spatial.refined.depth
    = surface.depth
  /-- The refined observation surface preserves its original numerical stage requirement. -/ initial_surface_le :
    initialSurface.index ≤ surface.index
  /-- The common numerical stage paying both acquired surfaces. -/ index : Nat
  /-- The common stage is exactly the maximum of the physical and observation stages. -/ index_eq : index = max
    spatial.refined.index surface.index

constructive_injectivity SurfaceAcquisition

namespace SurfaceAcquisition

/-- Choose the physical depth first, then refine the retained observation request to that same depth. -/
@[expose] def build : SurfaceAcquisition
  schedules initialSurface := by
  let spatial :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition.RequestedSurfaceRuns.acquireSpatial
    (Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition.RequestedSurfaceRuns.observationSchedules schedules
    initialSurface)
  have later : initialSurface.depth ≤ spatial.depths.depth :=
    (Nat.Order.le_max_right request.depth initialSurface.depth).trans spatial.depths.floor_le
  let surface := Hyperelliptic.Meshes.Newton.Surface.DepthRefinement.atDepth
    initialSurface spatial.depths.depth later
  exact ⟨spatial, surface, spatial.mesh_depth,
    Hyperelliptic.Meshes.Newton.Surface.DepthRefinement.atDepth_index_ge initialSurface _ later,
    max spatial.refined.index surface.index, rfl⟩

variable {schedules initialSurface} (acquired :
  SurfaceAcquisition schedules
  initialSurface)

/-- The acquired physical surface stage is bounded by the common numerical stage. -/
theorem physical_le : acquired.spatial.refined.index ≤ acquired.index := by
  rw [acquired.index_eq]
  exact Nat.Order.le_max_left _ _

/-- The acquired observation surface stage is bounded by the common numerical stage. -/
theorem surface_le : acquired.surface.index ≤ acquired.index := by
  rw [acquired.index_eq]
  exact Nat.Order.le_max_right _ _

/-- The original physical numerical floor survives both depth transports. -/
theorem initial_physical_le : request.index ≤ acquired.index :=
  (request.atDepth_index_ge _ (Nat.Order.le_max_left ..)).trans
    (acquired.spatial.surface_index_le.trans acquired.physical_le)

/-- Observation acquisition keeps every earlier numerical requirement. -/
theorem initial_observation_le : initialSurface.index ≤ acquired.index :=
  acquired.initial_surface_le.trans acquired.surface_le

/-- Both refinements preserve each original source query stage. -/
theorem sourceIndex_readback (outer : Fin prepared.occurrences.length) :
    (acquired.spatial.requests.get outer).sourceIndex = (schedules.get outer).sourceIndex :=
  (acquired.spatial.sourceIndex_readback outer).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_sourceIndex
      schedules _ (Nat.Order.le_max_left ..) outer)

/-- The synchronized mesh still pays the original parent-run depth. -/
theorem request_depth (outer : Fin prepared.occurrences.length) :
    (acquired.spatial.requests.get outer).depth = (schedules.get outer).depth :=
  (acquired.spatial.request_depth outer).trans
    (atDepth_depth schedules _ (Nat.Order.le_max_left ..) outer)

/-- Magnitude ownership is unchanged while the two geometries are synchronized. -/
theorem magnitude_readback (outer : Fin prepared.occurrences.length) :
    (acquired.spatial.requests.get outer).magnitude = (schedules.get outer).magnitude :=
  (acquired.spatial.magnitude_readback outer).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.atDepth_magnitude
      schedules _ (Nat.Order.le_max_left ..) outer)

/-- Each acquired physical occurrence uses the observation request's depth. -/
theorem occurrence_depth (outer : Fin prepared.occurrences.length) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence.RequestedOccurrenceRuns.mesh outer selected
      acquired.spatial.refined).depth = acquired.surface.depth :=
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRefinement.RequestedOccurrenceRuns.mesh_depth
    outer selected acquired.spatial.refined).trans acquired.same_depth

end SurfaceAcquisition
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
