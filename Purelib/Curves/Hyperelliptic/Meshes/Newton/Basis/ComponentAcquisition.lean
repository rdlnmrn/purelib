module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.NumericalAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RootAcquiredEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.ObservationComponents
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
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
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra

open Purelib.Curves

open Purelib

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! Acquire the reciprocal and face numerical banks for the computed component request. -/
open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {gridTarget radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation gridTarget radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured} {firstIndex : Fin genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)}

section SourceSurfaceAcquisition

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation component.prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {energyTarget coefficientTarget requested : Normalization.InverseRootPolynomial.Coordinate} {traceFloor floor
    seedIndex minimum : Nat}
  {seedInputs : retained.Inputs seedIndex}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
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

set_option genInjectivity false in
/-- Numerical banks are acquired once, independently of the coefficient vector.
The selected cap sample is read from the retained basis polynomial bank. -/
structure ComponentAcquisition where
  /-- The retained reciprocal basis samples at the acquired source index and collar box. -/ polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap acquired.index collar.box
  /-- The computed root-source readings using the exact retained first basis polynomial. -/ roots :
    Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings.RequestedSurfaceRuns.SourceSurfaceAcquisition.RootReadings
    acquired (polynomials.get firstIndex) polynomials energyFloor
  /-- The retained physical and observation numerical schedule on the acquired geometry and vertex allocation. -/
    numerical :
    NumericalAcquisition
    acquired.geometry vertices
  /-- The common face stage paying the requested floor and retained numerical schedule. -/ faceIndex : Nat
  /-- The face stage is exactly the maximum of the requested floor and numerical threshold. -/ face_eq : faceIndex = max
    faceFloor numerical.index
  /-- The cached numerical face bank at the retained face stage and original domains. -/ cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex
  /-- The dependent bank of triangle readings on these exact cached face rows and the original lifted mesh. -/ triangles
    : Data.Vector.DependentVector (fun row : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get row) lifted.mesh)

constructive_injectivity ComponentAcquisition

namespace ComponentAcquisition.mk

end ComponentAcquisition.mk

namespace ComponentAcquisition

/-- Acquire and retain the reciprocal basis samples, root readings, numerical schedule and common face bank.

The face stage is the maximum of the requested floor and numerical threshold. Triangle readings use these exact cached
rows, independently of later coefficient evaluation. -/
def build (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    ComponentAcquisition shared acquired
      vertices energyFloor faceFloor :=
  let polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    acquired.index collar.box := Data.Vector.DependentVector.ofFn fun row =>
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap (Periods.PeriodMatrix.standardDifferential row)
      acquired.index collar.box
  let roots :=
    SourceRootReadings.RequestedSurfaceRuns.SourceSurfaceAcquisition.RootReadings.build
    acquired (polynomials.get firstIndex) polynomials energyFloor branch
  let numerical :=
    NumericalAcquisition.build
    acquired.geometry vertices
  let faceIndex := max faceFloor numerical.index
  let cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains faceIndex :=
    Data.Vector.DependentVector.ofFn fun row =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build
      (Periods.PeriodMatrix.standardDifferential row) faceIndex domains
  let triangles := Data.Vector.DependentVector.ofFn fun row : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.build (cache.get row) lifted.mesh
  ⟨polynomials, roots, numerical, faceIndex, rfl, cache, triangles⟩

variable {shared acquired vertices energyFloor faceFloor}
  (samples :
    ComponentAcquisition
    shared acquired vertices energyFloor faceFloor)

/-- The numerical acquisition threshold is bounded by the retained face stage. -/
theorem face_paid : samples.numerical.index ≤ samples.faceIndex := by
  rw [samples.face_eq]
  exact Nat.Order.le_max_right _ _

/-- The requested face floor is bounded by the retained face stage. -/
theorem floor_paid : faceFloor ≤ samples.faceIndex := by
  rw [samples.face_eq]
  exact Nat.Order.le_max_left _ _

/-- The complete component estimate consumes its acquired banks at their certified stages. -/
theorem energy_upper (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (member : ∀ outer, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
      component.prepared.occurrences outer ∈ (preparations.get firstIndex).occurrences)
    (positive : 0 < requested) {allowance : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤
      allowance)
    (paid : requested ≤ 16 * allowance ^ 2)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    let evaluated :=
      Hyperelliptic.Meshes.Newton.Basis.SurfaceEvaluation.RequestedSurfaceRuns.SurfaceAcquisition.Evaluation.build
      acquired.geometry vertices samples.numerical samples.cache coefficients member samples.face_paid
    (component.prepared.observedSides evaluated.observed -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents.componentCachedEndpoints component
      samples.cache coefficients +
      Path.PairedIncrementArea.area (component.program.indexed.map (fun edge =>
        Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (samples.triangles.get
            row).values edge)))).im / 4 ≤
      (5 * energyTarget + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
  Hyperelliptic.Meshes.Newton.Basis.RootAcquiredEnergy.CommonBasisRequest.Sampled.root_acquired_component_energy_upper
    shared acquired samples.roots samples.numerical samples.cache
    samples.face_paid member (fun row => samples.triangles.get row) positive nonnegative paid branch

end ComponentAcquisition
end SourceSurfaceAcquisition
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
