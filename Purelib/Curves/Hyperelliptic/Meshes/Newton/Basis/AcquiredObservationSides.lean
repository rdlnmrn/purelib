module
import Purelib.Tactic.Ring
import Purelib.LinearAlgebra.Gaussian.Energy
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedEndpoints
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

public section

/-! Match acquired occurrence sides to the retained observation boundary samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.AcquiredObservationSides

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
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    (Periods.PeriodMatrix.standardDifferential firstIndex)} {prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

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
  prepared} {index : Nat} {inputs : retained.Inputs index}
  {traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.Traces
    (prepared := prepared) (shared.source.select firstIndex) request} {faceIndex : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {requested :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {schedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    (shared.source.select firstIndex) request retained inputs requested minimum}
  {vertices : (outer : Fin prepared.occurrences.length) → Fin
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

include faces wholePerimeters sameDepth

/-- Acquired source occurrences read exactly the observation boundary's complete side areas. -/
theorem originalSides_eq_observation :
  PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.originalSides
  samples =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn fun outer =>
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
      let reading := (observed.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position
      let value := match occurrence.sideOccurrence.side with
        | .bottom => reading.bottom.originalArea
        | .right => reading.right.originalArea
        | .top => reading.top.originalArea
        | .left => reading.left.originalArea
      if occurrence.sourceForward then value else -value) := by
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.OfFn.Basic.ofFn_congr
  intro outer
  let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer
  let reading := (observed.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position
  have depth := sameDepth.trans (surface.depth_eq occurrence.sideOccurrence.sheet).symm
  apply congrArg (fun value => if occurrence.sourceForward then value else -value)
  have each (side : Meshes.GridLiftedDualSteps.GridSide) :
      ((samples.get outer).samples.get (traces.get outer) cache coefficients side).originalArea =
        match side with
        | .bottom => reading.bottom.originalArea
        | .right => reading.right.originalArea
        | .top => reading.top.originalArea
        | .left => reading.left.originalArea := by
    cases side with
    | bottom =>
      exact Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters.common_bottom_sample_eq shared request depth reading
        ((faces.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position)
        (traces.get outer) (wholePerimeters occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
        ((samples.get outer).samples.get (traces.get outer) cache coefficients .bottom)
    | right =>
      exact Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters.common_right_sample_eq shared request depth reading
        ((faces.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position)
        (traces.get outer) (wholePerimeters occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
        ((samples.get outer).samples.get (traces.get outer) cache coefficients .right)
    | top =>
      exact Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters.common_top_sample_eq shared request depth reading
        ((faces.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position)
        (traces.get outer) (wholePerimeters occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
        ((samples.get outer).samples.get (traces.get outer) cache coefficients .top)
    | left =>
      exact Hyperelliptic.Meshes.Newton.Basis.RequestedPerimeters.common_left_sample_eq shared request depth reading
        ((faces.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position)
        (traces.get outer) (wholePerimeters occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet)
        ((samples.get outer).samples.get (traces.get outer) cache coefficients .left)
  exact each occurrence.sideOccurrence.side

/-- The acquired component uses exactly its retained occurrence signs in the observed side sum. -/
theorem originalSides_eq_observedSides :
  PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.originalSides
  samples = prepared.observedSides observed := by
  rw
    [originalSides_eq_observation
    shared samples observed faces whole wholePerimeters sameDepth]
  unfold
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.observedSides
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  have signs := Data.List.OfFn.Basic.ofFn_congr (fun outer : Fin prepared.occurrences.length => show
      (let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer
       let reading := (observed.get occurrence.sideOccurrence.sheet).get occurrence.sideOccurrence.position
       let value := match occurrence.sideOccurrence.side with
         | .bottom => reading.bottom.originalArea
         | .right => reading.right.originalArea
         | .top => reading.top.originalArea
         | .left => reading.left.originalArea
       if occurrence.sourceForward then value else -value) =
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sideOccurrence
        (Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide observed
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
            outer).sideOccurrence.position
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
            outer).sideOccurrence.sheet
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
            outer).sideOccurrence.side) from by
    dsimp only
    cases side : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.side <;>
      cases backward : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        prepared.occurrences outer).sideOccurrence.backward <;>
      simp only
        [PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceForward,
        Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented,
        Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide, side, backward,
        if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .top ∨
          Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .left),
        if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .top ∨
          Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .left),
        if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .top ∨
          Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .left)),
        if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .top ∨
          Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .left)),
        if_pos (Eq.refl true), if_neg (by decide : ¬ false = true), -eq_self, -iff_self] <;>
        first | rfl | ring1)
  apply signs.trans
  exact (Data.List.OfFn.Basic.map_ofFn).symm.trans
    (congrArg (List.map fun occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
      occurrence.sideOccurrence
      (Hyperelliptic.Meshes.Newton.Basis.ObservationComponents.observationSide observed
        occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))
      (Data.List.OfFn.Basic.ofFn_getElem prepared.occurrences))

/-- Match the complete acquired boundary to the observed component without losing its centering or joining terms. -/
theorem boundary_eq_observation :
    Path.PairedIncrementArea.area
      (List.ofFn (fun outer => (List.ofFn
        (PuncturedGrid.Exterior.Basis.PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        samples.entries outer)).flatten)).flatten =
      prepared.observedSides observed -
        PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.endpointSides
        samples +
        PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.joiningArea
        samples := by
  have boundary :=
    PuncturedGrid.Exterior.Basis.RequestedPerimeterBoundary.RequestedSurfaceRuns.PhysicalSamples.boundary_eq
    samples
  rw
    [originalSides_eq_observedSides
    shared samples observed faces whole wholePerimeters sameDepth] at boundary
  exact boundary

end PhysicalSamples
end RequestedSurfaceRuns
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.AcquiredObservationSides
