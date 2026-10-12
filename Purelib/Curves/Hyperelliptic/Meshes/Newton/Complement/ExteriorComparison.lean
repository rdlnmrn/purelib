module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.RootContinuation.NewtonRemainingBandPayment
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Tactic.Ring

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

public section

/-! The paid annular complement reduces to the unchanged exterior on the same cache. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorComparison

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann
open Purelib.RootIsolation

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} (allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest
    preparation target radius)
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames allocated.family.single.grid.shrunk.prepared.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    allocated.family.single.grid.faces.regulars} {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions
    observations allocated.family.single.grid}
  {coarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Fraction.Rational}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage} {coefficients
    : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {lifted : Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted}
  {requests : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error} {traces :
    Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  {position : Fin allocated.family.single.grid.faces.regulars.length} {side : Meshes.GridLiftedDualSteps.GridSide}

open Purelib.Data.Rat.Fraction.Compatibility

namespace RemainingBandRequest

variable {floor : Nat} {allowance : Fraction.Rational}

/-- Compare the paid original annular-complement boundary with its actual exterior and cached endpoint correction.

The retained band request, synchronized face samples and same coefficient vector determine both sides at the common late
stage. -/
theorem exterior_accurate
    (request : Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest
      (grid := allocated.family.single.grid) excision traces floor)
    (later : request.index ≤ stage) (samples :
      Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces cache
      coefficients)
    {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies requests (cache :=
      cache) (coefficients := coefficients)}
    {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters requests assemblies}
      (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
    (positive : 0 < allowance)
    (targetLe : target ≤
      BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance) :
    Data.Gaussian.Norm.Basic.normSq
      (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors -
      (RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentBoundary
        samples neighbors .exterior -
        RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
          neighbors .exterior
          (PerimeterSamples.cachedEndpointSideSum
          cache coefficients))) ≤
      (4 * (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
  have bound := RootContinuation.NewtonRemainingBandPayment.SynchronizedSurfaceRequests.RemainingBandRequest.paid
    allocated request later samples neighbors positive targetLe
  rw
    [ExteriorReadback.SynchronizedSurfaceRequests.PerimeterSamples.remainingExterior_cached
    samples excision faces neighbors] at bound
  exact bound

/-- Transport the paid original complement-boundary error into a scalar energy lower bound.

The actual exterior and retained endpoint chords remain explicit, and the allowance is scaled by the same coefficient
norm. -/
theorem exterior_energy_lower
    (request : Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest
      (grid := allocated.family.single.grid) excision traces floor)
    (later : request.index ≤ stage) (samples :
      Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces cache
      coefficients)
    {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies requests (cache :=
      cache) (coefficients := coefficients)}
    {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters requests assemblies}
      (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
    (positive : 0 < allowance)
    (targetLe : target ≤
      BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance)
    (energy : Gaussian.Basic.Canonical) :
    (energy +
      CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors).im / 4 -
        allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      (energy +
        (RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentBoundary
        samples neighbors .exterior -
        RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples.componentSum
          neighbors .exterior
          (PerimeterSamples.cachedEndpointSideSum
          cache coefficients))).im / 4 := open Purelib.Algebra in by
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Gaussian.Norm.Basic.normSq_nonneg (coefficients row))
    have same := FiniteSum.Fin.sumFin_congr
      (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
    change 0 ≤ FiniteSum.Fin.sumFin (fun row => (coefficients row).normSq)
    rw [← same]
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  apply Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le _ _ _
    (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le normNonnegative)
  have cancel (first last : Gaussian.Basic.Canonical) : (energy + first) - (energy + last) = first - last := by ring1
  rw [cancel]
  exact
    exterior_accurate
    allocated request later samples faces neighbors positive targetLe

end RemainingBandRequest
end SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorComparison
