module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.NumericalAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.RootAcquiredEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib.Curves

open Purelib.Riemann

public section

/-! Compute a common tail for the source comparison, positive surface, contacts and remaining boundary. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

open Purelib

open Purelib.Data.Rat

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

  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)

  (compatible : Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions) (allowance :
    Normalization.InverseRootPolynomial.Coordinate)

set_option genInjectivity false in
/-- Retain all coefficient-independent requests before choosing a numerical face stage. -/
structure CoercivitySchedule where
  /-- The cached reciprocal basis polynomials acquired at the retained source index and collar box. -/ polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap acquired.index collar.box
  /-- The computed root-source readings and radial fans using these exact polynomial samples. -/ roots :
    Hyperelliptic.Meshes.Newton.Basis.SourceRootReadings.RequestedSurfaceRuns.SourceSurfaceAcquisition.RootReadings
    acquired (polynomials.get firstIndex) polynomials energyFloor
  /-- The shared physical and observation owner schedule for the acquired geometry. -/ numerical :
    NumericalAcquisition
    acquired.geometry vertices
  /-- The positive surface-energy request using the retained common allowance. -/ energy :
    Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests.GlobalEnergyRequest acquired.geometry.surface
    allowance allowance allowance
  /-- The original contact request on the retained mesh, compatibility witnesses and perimeter traces. -/ contacts :
    RootContinuation.NewtonGlobalContactRequest.SynchronizedSurfaceRequests.GlobalContactRequest
    acquired.geometry.surface compatible lifted.mesh
    (Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build acquired.geometry.surface)
      allowance faceFloor
  /-- The retained remaining-boundary request on the original excision and perimeter traces. -/ remaining :
    Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest excision
    (Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build acquired.geometry.surface)
    faceFloor
  /-- The common face stage paying the floor and all retained numerical requests. -/ index : Nat
  /-- The stage is exactly the finite maximum of the floor, owners, energy, contact and remaining-boundary thresholds.
  -/
  index_eq : index = max faceFloor (max numerical.index (max energy.index (max contacts.index remaining.index)))

constructive_injectivity CoercivitySchedule

namespace CoercivitySchedule

/-- Compute and retain all coefficient-independent source, geometry, energy, contact and remaining-boundary requests.

The common face stage is their finite maximum. Every later coefficient evaluation consumes these exact cached polynomial
and request banks. -/
@[expose] def build (positive : 0 < allowance) (branch :
  Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    CoercivitySchedule shared acquired
      vertices energyFloor faceFloor excision compatible allowance :=
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
  let energy := Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests.GlobalEnergyRequest.build
    acquired.geometry.surface allowance allowance allowance positive positive positive
  let traces := Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build
    acquired.geometry.surface
  let contacts := RootContinuation.NewtonGlobalContactRequest.SynchronizedSurfaceRequests.GlobalContactRequest.build
    acquired.geometry.surface compatible lifted.mesh traces allowance positive faceFloor
  let remaining :=
    Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest.build excision
    traces faceFloor
  ⟨polynomials, roots, numerical, energy, contacts, remaining,
    max faceFloor (max numerical.index (max energy.index (max contacts.index remaining.index))), rfl⟩

variable {shared acquired vertices energyFloor faceFloor excision compatible allowance}
  (schedule : CoercivitySchedule
    shared acquired vertices energyFloor faceFloor excision compatible allowance)

/-- The prescribed face floor is bounded by the common coercivity stage. -/
theorem floor_le : faceFloor ≤ schedule.index := by
  rw [schedule.index_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- The retained physical and observation owner threshold is bounded by the common coercivity stage. -/
theorem numerical_le : schedule.numerical.index ≤ schedule.index := by
  rw [schedule.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The retained positive surface-energy threshold is bounded by the common coercivity stage. -/
theorem energy_le : schedule.energy.index ≤ schedule.index := by
  rw [schedule.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _
    _))

/-- The retained contact threshold is bounded by the common coercivity stage. -/
theorem contacts_le : schedule.contacts.index ≤ schedule.index := by
  rw [schedule.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _
    _).trans (Data.Nat.Order.le_max_right _ _)))

/-- The retained remaining-boundary threshold is bounded by the common coercivity stage. -/
theorem remaining_le : schedule.remaining.index ≤ schedule.index := by
  rw [schedule.index_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _
    _).trans (Data.Nat.Order.le_max_right _ _)))

/-- The acquired observation surface threshold is bounded by the common coercivity stage. -/
theorem observation_le : acquired.geometry.surface.index ≤ schedule.index :=
  schedule.numerical.observation_le.trans schedule.numerical_le

end CoercivitySchedule
end SourceSurfaceAcquisition
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
