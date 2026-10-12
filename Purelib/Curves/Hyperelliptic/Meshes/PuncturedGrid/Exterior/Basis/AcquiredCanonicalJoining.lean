module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredJoiningReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalJoiningWord
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves

open Purelib.Integration

open Purelib.Riemann

public section

/-! The actual acquired physical joining polygon is Newton's canonical component polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredCanonicalJoining

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank (Data values)

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

variable (readings : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  (cache.get row) lifted.mesh)

/-- Each acquired occurrence contributes the corresponding canonical edge increment. -/
theorem acquired_canonical_word :
    (List.ofFn fun outer => Path.PairedIncrementArea.total
      (List.ofFn
        (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths

          (RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
          selected request traces cache coefficients schedules owners perimeters member face later).entries
          outer)).flatten) =
      program.indexed.map (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row =>
        coefficients row *
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge)) :=
          by
  have totals := Data.List.OfFn.Basic.ofFn_congr (fun outer =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredJoiningReadback.RequestedSurfaceRuns.acquired_total
      selected request traces cache coefficients schedules owners perimeters member face later outer)
  exact totals.trans
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.cached_increment_word
    prepared whole member cache coefficients readings)

/-- The acquired joining polygon retains all canonical cross-edge contributions. -/
theorem acquired_canonical_joiningArea :

      RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.joiningArea
      (RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
      selected request traces cache coefficients schedules owners perimeters member face later) =
      Path.PairedIncrementArea.area (program.indexed.map (fun edge =>
        Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge)))
            :=
  congrArg Path.PairedIncrementArea.area

      (acquired_canonical_word
      selected request traces cache coefficients schedules owners perimeters member face later readings)

/-- The full acquired boundary has its canonical joining polygon and exact centering correction. -/
theorem acquired_canonical_boundary :
    let physical :=
      RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
      selected request traces cache coefficients schedules owners perimeters member face later
    Path.PairedIncrementArea.area
      (List.ofFn (fun outer => (List.ofFn
        (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        physical.entries outer)).flatten)).flatten =

        RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.originalSides
        physical -
        RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
        physical +
        Path.PairedIncrementArea.area (program.indexed.map (fun edge =>
          Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
              edge))) := by
  have boundary :=
    RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.boundary_eq
    (RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
    selected request traces cache coefficients schedules owners perimeters member face later)
  rw
    [acquired_canonical_joiningArea
    selected request traces cache coefficients schedules owners perimeters member face later readings] at boundary
  exact boundary

end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredCanonicalJoining
