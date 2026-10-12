module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredSampleTotals
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib.Curves

open Purelib

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! The acquired joining polygon uses exact original-corner occurrence displacements. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredJoiningReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOccurrence

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

open
  RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
  (entries entry_sideArea)

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns

open
  RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
  (entries)

variable {whole :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : SourceCuts whole previous)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)

variable (traces :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces (prepared :=
  prepared) selected request) {stage : Nat} (cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {requested :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    selected request retained inputs requested minimum)
  {vertices : (outer : Fin prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities selected
    request outer) → Nat}
  (owners :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    schedules
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
    selected request) vertices)
  (perimeters :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    selected request traces cache)

variable (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer ∈ whole.occurrences)
  (face :
    RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage
    owners request.index) (later : face.stage ≤ stage)

/-- Component assembly retains the very parent path stored by occurrence acquisition. -/
theorem acquired_parent_path (outer : Fin prepared.occurrences.length)
    (parent : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :

      PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths

        (RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
        selected request traces cache coefficients schedules owners perimeters member face later).entries outer parent =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalSample.RequestedOccurrenceRuns.acquireSample
        retained inputs outer selected request (traces.get outer) cache
        (perimeters.get outer) coefficients (schedules.get outer) (owners.get outer)
        (member outer) ((face.owner_le outer).trans later)).bank.physical parent := by
  dsimp only
    [PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths,
    RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples.entries]
  rw [Data.Vector.DependentVector.ofFn_get]
  dsimp only
    [RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Every acquired occurrence total is the signed original corner displacement. -/
theorem acquired_total (outer : Fin prepared.occurrences.length) :
    Path.PairedIncrementArea.total (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths

        (RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
        selected request traces cache coefficients schedules owners perimeters member face later).entries
        outer)).flatten =
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
        (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.sub
        Topology.Polygon.Stokes.PrimitivePoint.zero total := by
  have paths := Data.List.OfFn.Basic.ofFn_congr (fun parent =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredJoiningReadback.RequestedSurfaceRuns.acquired_parent_path
      selected request traces cache coefficients schedules owners perimeters member face later outer parent)
  rw [paths]
  exact
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredSampleTotals.RequestedOccurrenceRuns.acquireSample_total
    retained inputs outer selected request (traces.get outer) cache
    (perimeters.get outer) coefficients (schedules.get outer) (owners.get outer)
    (member outer) ((face.owner_le outer).trans later)

/-- Preserve the whole joining polygon, including its cross-occurrence wedges. -/
theorem acquired_joiningArea :

      RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.joiningArea
      (RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
      selected request traces cache coefficients schedules owners perimeters member face later) =
      Path.PairedIncrementArea.area (List.ofFn fun outer =>
        let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
          prepared.occurrences outer
        let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
          (lifted := lifted) cache coefficients
          occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
        if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.sub
          Topology.Polygon.Stokes.PrimitivePoint.zero total) := by
  apply congrArg Path.PairedIncrementArea.area
  apply Data.List.OfFn.Basic.ofFn_congr
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredJoiningReadback.RequestedSurfaceRuns.acquired_total
    selected request traces cache coefficients schedules owners perimeters member face later

end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredJoiningReadback
