module
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RootAcquiredEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SewnEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CanonicalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RamifiedComponent
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.NumericalAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
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
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

public section

/-! Both boundary estimates use one acquired source bank and one later face cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivityBounds

open Purelib

open Purelib.Data.Rat

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

namespace CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition
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

  (compatible : Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions) (allowance :
    Normalization.InverseRootPolynomial.Coordinate)

namespace CoercivitySchedule
variable {allocated shared acquired vertices energyFloor faceFloor excision compatible allowance}
  (schedule : CoercivitySchedule shared
    acquired vertices energyFloor faceFloor excision compatible allowance)
  {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    component.prepared.occurrences outer ∈ (preparations.get firstIndex).occurrences)
  (later : schedule.index ≤ stage)

/-- The same retained evaluation supplies both the upper and lower boundary estimates. -/
@[expose] def evaluate :=
  Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.Evaluation.build
  acquired.geometry vertices schedule.numerical cache coefficients member
  (schedule.numerical_le.trans later)

variable (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
  (positive : 0 < allowance)
  (triangles : Data.Vector.DependentVector (fun row : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get row) lifted.mesh))

include positive

/-- Independent observation positivity reaches the actual sewn complement on this face cache. -/
theorem sewn_lower
    {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation lifted.cutPolygon domains}
      {sewingFloor : Nat}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request prepared
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance)
        sewingFloor)
    (sewingLater : sewing.index ≤ stage)
    (surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces lifted.cutPolygon.patch (fun row =>
      (triangles.get row).values))
    (pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces)
    (selected : Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples surfaces pairs
      (fun source => !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
        source)))) :
    (2 * (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - allowance - allowance -
      allowance) - allowance - allowance) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      (selected.energy coefficients +
        Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
        excision

          (evaluate
          schedule cache coefficients member later).observed neighbors).im / 4 := by
  let evaluated :=
    evaluate
    schedule cache coefficients member later
  exact Hyperelliptic.Meshes.Newton.Complement.SewnEnergy.SynchronizedSurfaceRequests.remaining_sewn_energy_lower
    excision schedule.energy sewing (schedule.energy_le.trans later) sewingLater
    (Data.Vector.DependentVector.ofFn fun sheet => (acquired.geometry.surface.entries.get sheet).readings cache)
    Hyperelliptic.Integration.Energy.Prepared.canonicalSurfaceFace evaluated.faces evaluated.observed neighbors positive
      schedule.contacts
    (schedule.contacts_le.trans later) triangles surfaces pairs selected positive

/-- The acquired ramified source bounds the complete remaining boundary, retaining its canonical polygon. -/
theorem remaining_upper
    (canonical : component =
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build
      regular domains
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
        (Periods.PeriodMatrix.standardDifferential firstIndex) 0))
    (requestedPositive : 0 < requested) (paid : requested ≤ 16 * allowance ^ 2)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (targetLe : gridTarget ≤
      Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance) :

      (Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision

          (evaluate
          schedule cache coefficients member later).observed neighbors +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word =>
        Path.PairedIncrementArea.area (word.map (fun edge =>
          Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (triangles.get row).values
              edge)))))).im / 4 ≤
      (5 * energyTarget + allowance + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
        := by
  let evaluated :=
    evaluate
    schedule cache coefficients member later
  have singleton :
    (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
    (lifted := lifted) regular domains
      (Periods.PeriodMatrix.standardDifferential firstIndex)).components = [component] :=

      (ExteriorProgram.AllSurfacePreparation.built_components_ramified
      branch).trans (congrArg List.singleton canonical.symm)
  have bound :=
    Complement.CanonicalEnergy.SynchronizedSurfaceRequests.RemainingBandRequest.canonical_energy_upper
    allocated schedule.remaining (schedule.remaining_le.trans later)
    evaluated.observed evaluated.faces neighbors positive targetLe (fun row => triangles.get row)
    (componentAllowance := 5 * energyTarget + allowance)
    (fun other present => by
      rw [singleton] at present
      have same := Data.List.Membership.mem_singleton.mp present
      cases same
      exact
        RootAcquiredEnergy.CommonBasisRequest.Sampled.root_acquired_component_energy_upper
        shared acquired schedule.roots
        schedule.numerical cache (schedule.numerical_le.trans later) member (fun row => triangles.get row)
        requestedPositive positive.le paid branch)
  simp only [singleton, List.length_singleton, Nat.cast_one, one_mul, -eq_self, -iff_self] at bound
  exact bound

end CoercivitySchedule
end CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivityBounds
