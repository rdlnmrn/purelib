module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedEndpoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.AcquiredObservationSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.AcquiredCanonicalJoining
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves

open Purelib.Integration

open Purelib.Riemann

public section

/-! Identify an actual acquired component with the canonical observed boundary expression. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.AcquiredComponentReadback

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {firstIndex : Fin genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace RequestedSurfaceRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

variable {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {preparations : Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains}
  (shared : Branches.NewtonSharedExteriorCuts.SharedExteriorCuts partitions preparations)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains
      (shared.source.select firstIndex).cuts sheet coarseDepth) fixed meshTarget)

variable {request} {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  component.prepared} {index : Nat} {inputs : retained.Inputs index}
  {traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces
    (prepared := component.prepared) (shared.source.select firstIndex) request} {faceIndex : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {requested :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    (shared.source.select firstIndex) request retained inputs requested minimum}
  {vertices : (outer : Fin component.prepared.occurrences.length) → Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities
    (shared.source.select firstIndex) request outer) → Nat}
  {owners :
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.SharedOwnerBanks
    schedules
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
    (shared.source.select firstIndex) request) vertices}
  {perimeters :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Perimeters
    (shared.source.select firstIndex) request traces cache}

namespace PhysicalSamples

variable (samples :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.PhysicalSamples
  (shared.source.select firstIndex) request traces cache coefficients schedules owners perimeters)

open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests

variable {pieceDepth : Nat} {surfaceFixed : (sheet : Fin 2) →
  RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
  {error : Normalization.InverseRootPolynomial.Coordinate}
  {surface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
    (fun sheet => Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet pieceDepth) surfaceFixed error}
  {observationTraces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces surface}
  (observed : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples surface
    observationTraces cache coefficients)
  {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies surface (cache :=
    cache) (coefficients := coefficients)}
  {observationPerimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters surface
    assemblies}
  (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces surface observationPerimeters)
  (whole : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) →
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly ((request.entries.get
      sheet).meshes.entries.get position)
      (Hyperelliptic.Meshes.Newton.Surface.SeamAreas.seamValues (sheet := sheet) cache coefficients position))
  (wholePerimeters : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) →
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter (whole position sheet))
  (sameDepth : request.depth = surface.depth)

/-- Acquired endpoint chords are exactly the retained component's original cached endpoints. -/
theorem endpointSides_eq_component :
  PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
  samples =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
      coefficients := open Data in by
  rw
    [PuncturedGrid.Exterior.Basis.RequestedEndpoints.RequestedSurfaceRuns.PhysicalSamples.endpointSides_eq_oriented
    samples]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  exact Data.List.OfFn.Basic.map_ofFn.symm.trans
    (congrArg (List.map fun occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
      occurrence.sideOccurrence
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter.cachedEndpoint cache
        coefficients occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))
      (Data.List.OfFn.Basic.ofFn_getElem component.prepared.occurrences))

include faces wholePerimeters sameDepth

/-- Read the complete physical boundary on one observed component, preserving its joining polygon. -/
theorem boundary_eq_component :
    Path.PairedIncrementArea.area
      (List.ofFn (fun outer => (List.ofFn
        (PuncturedGrid.Exterior.Basis.PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        samples.entries outer)).flatten)).flatten =
      component.prepared.observedSides observed -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
        coefficients +

          PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.joiningArea
          samples := by
  have boundary :=
    AcquiredObservationSides.RequestedSurfaceRuns.PhysicalSamples.boundary_eq_observation
    shared samples observed faces whole wholePerimeters sameDepth
  rw
    [endpointSides_eq_component
    shared samples] at boundary
  exact boundary

variable (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  component.prepared.occurrences outer ∈ (preparations.get firstIndex).occurrences)
  (face :
    PuncturedGrid.Exterior.Basis.RunFaceSynchronization.CommonBasisPreparation.ParentRunSchedules.FaceStage
    owners request.index) (later : face.stage ≤ faceIndex)
  (triangles : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
    (cache.get row) lifted.mesh)

/-- The actual acquisition supplies the canonical joining polygon in the observed component boundary. -/
theorem acquired_boundary_eq_component :
    let physical :=
      PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
      (shared.source.select firstIndex) request traces cache
      coefficients schedules owners perimeters member face later
    Path.PairedIncrementArea.area
      (List.ofFn (fun outer => (List.ofFn
        (PuncturedGrid.Exterior.Basis.PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        physical.entries outer)).flatten)).flatten =
      component.prepared.observedSides observed -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component cache
        coefficients +
        Path.PairedIncrementArea.area (component.program.indexed.map (fun edge =>
          Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (triangles row).values
              edge))) := by
  let physical :=
    PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.acquirePhysicalSamples
    (shared.source.select firstIndex) request traces cache
    coefficients schedules owners perimeters member face later
  have boundary :=
    boundary_eq_component
    shared physical observed faces whole wholePerimeters sameDepth
  have joining :=
    PuncturedGrid.Exterior.Basis.AcquiredCanonicalJoining.RequestedSurfaceRuns.acquired_canonical_joiningArea
    (shared.source.select firstIndex) request traces cache
    coefficients schedules owners perimeters member face later triangles
  change
    PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.joiningArea
    physical = _ at joining
  rw [joining] at boundary
  exact boundary

end PhysicalSamples
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.AcquiredComponentReadback
