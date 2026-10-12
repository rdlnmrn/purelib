module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ComponentAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CanonicalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RamifiedComponent
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Pay the remaining-band comparison at the acquired odd-component numerical stage. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceComponent AllSurfacePreparation)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {gridTarget radius :
    Normalization.InverseRootPolynomial.Coordinate}
  (allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation gridTarget
    radius)
  {lifted : Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured} {firstIndex : Fin genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.family.single.grid.faces.regulars}
  {component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)}

section _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RemainingAcquisition.SourceSurfaceAcquisition

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation component.prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {energyTarget coefficientTarget requested : Normalization.InverseRootPolynomial.Coordinate} {traceFloor floor
    seedIndex minimum : Nat}
  {seedInputs : retained.Inputs seedIndex}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations allocated.family.single.grid}
  {preparations : Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains}
  (shared : Branches.NewtonSharedExteriorCuts.SharedExteriorCuts partitions preparations)
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {meshTarget : Normalization.InverseRootPolynomial.Coordinate}
  {meshRequest : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains
      (shared.source.select firstIndex).cuts sheet coarseDepth) fixed meshTarget}
  {seedSchedules : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    (shared.source.select firstIndex) meshRequest retained seedInputs requested minimum}
  {pieceDepth : Nat} {surfaceFixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights
    domains sheet}
  {error : Normalization.InverseRootPolynomial.Coordinate}
  {initialSurface : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests
    (fun sheet => Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet pieceDepth) surfaceFixed error}
  (acquired : SourceSurfaceAcquisition
    seedSchedules initialSurface basis energyTarget coefficientTarget traceFloor floor)

  (vertices : (outer : Fin component.prepared.occurrences.length) →
    Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities
      (shared.source.select firstIndex) acquired.geometry.spatial.refined outer) → Nat)
  (energyFloor faceFloor : Nat)

  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted)

set_option genInjectivity false in
/-- The face acquisition is delayed until the remaining-band request has computed its floor. -/
structure RemainingAcquisition where
  /-- The remaining-boundary comparison request on the original excision and acquired perimeter traces. -/ remaining :
    Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest excision
    (Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build acquired.geometry.surface)
    faceFloor
  /-- The retained component numerical bank whose face floor pays this exact remaining-boundary request. -/ samples :
    ComponentAcquisition shared acquired
    vertices energyFloor remaining.index

constructive_injectivity RemainingAcquisition

namespace RemainingAcquisition

/-- Prepare the remaining-boundary request before acquiring the component face samples.

The component acquisition uses the request threshold as its face floor, retaining the original excision, source geometry
and odd branch witness. -/
def build (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    RemainingAcquisition allocated
      shared acquired vertices energyFloor faceFloor excision :=
  let remaining :=
    Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest.build excision
    (Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build acquired.geometry.surface)
    faceFloor
  ⟨remaining, ComponentAcquisition.build
    shared acquired vertices energyFloor remaining.index branch⟩

variable {allocated shared acquired vertices energyFloor faceFloor excision}
  (data :
    RemainingAcquisition
    allocated shared acquired vertices energyFloor faceFloor excision)

/-- The retained component face stage pays the remaining-boundary request threshold. -/
theorem remaining_paid : data.remaining.index ≤ data.samples.faceIndex := data.samples.floor_paid

open Purelib.Data.List in
/-- One canonical odd component supplies the complete remaining-boundary upper estimate. -/
theorem energy_upper (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
      component.prepared.occurrences outer ∈ (preparations.get firstIndex).occurrences)
    (canonical : component =
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build
      regular domains
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
        (Periods.PeriodMatrix.standardDifferential firstIndex) 0))
    (positive : 0 < requested) {allowance bandAllowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative :
      0 ≤ allowance)
    (paid : requested ≤ 16 * allowance ^ 2)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
    (bandPositive : 0 < bandAllowance)
    (targetLe : gridTarget ≤
      Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) bandAllowance) :
    let evaluated :=
      Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.Evaluation.build
      acquired.geometry vertices data.samples.numerical data.samples.cache
      coefficients member data.samples.face_paid

    (Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision evaluated.observed neighbors +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word =>
        Path.PairedIncrementArea.area (word.map (fun edge =>
          Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (data.samples.triangles.get
              row).values edge)))))).im / 4 ≤
      (5 * energyTarget + allowance + bandAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients := by
  let evaluated :=
    Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.Evaluation.build
    acquired.geometry vertices data.samples.numerical data.samples.cache
    coefficients member data.samples.face_paid
  have singleton :
    (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
    (lifted := lifted) regular domains
      (Periods.PeriodMatrix.standardDifferential firstIndex)).components = [component] :=

        (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.built_components_ramified
      branch).trans (congrArg List.singleton canonical.symm)
  have bound :=
    Complement.CanonicalEnergy.SynchronizedSurfaceRequests.RemainingBandRequest.canonical_energy_upper
    allocated data.remaining data.remaining_paid evaluated.observed evaluated.faces
    neighbors bandPositive targetLe (fun row => data.samples.triangles.get row)
    (componentAllowance := 5 * energyTarget + allowance)
    (fun other present => by
      rw [singleton] at present
      have same := Membership.mem_singleton.mp present
      cases same
      exact data.samples.energy_upper coefficients member positive nonnegative paid branch)
  simp only [singleton, List.length_singleton, Nat.cast_one, one_mul] at bound
  exact bound

end RemainingAcquisition
end _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RemainingAcquisition.SourceSurfaceAcquisition
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
