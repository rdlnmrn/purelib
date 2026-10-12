module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Tactic.Ring

@[expose] public section

/-! The original all-hole radius allocation pays the retained boundary energy. -/

namespace Purelib.Riemann.RootContinuation.NewtonRemainingBandPayment

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests (FamilyFineAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (outerCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} (allocated :
    FamilyFineAreaRequest preparation target
    radius)
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    allocated.family.single.grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    allocated.family.single.grid.faces.regulars} {partitions : SurfacePartitions observations
    allocated.family.single.grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests
  (RemainingBandRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest
  (accurate)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (remainingBoundaryCentered)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests
  (remainingBoundaryTarget remainingBoundaryTarget_paid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {lifted : LiftedPuncturedGrid allocated.family.single.grid.punctured}
  {excision : AllHoleExcision allocated.family.single.grid
    lifted}
  {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  {position : Fin allocated.family.single.grid.faces.regulars.length} {side : GridSide}

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Data in
/-- Dividing a nonnegative rational by a denominator at least one cannot increase it. -/
private theorem divide_le_self {value denominator : Rat.Fraction.Rational}
    (nonnegative : 0 ≤ value) (denominatorLe : 1 ≤ denominator) : value / denominator ≤ value := by
  have bound := Rat.Fraction.Order.Field.div_le_div_of_nonneg_left_direct nonnegative (by
      decide : (0 : Rat.Fraction.Rational) < 1) denominatorLe
  simpa only [Rat.Fraction.Field.div_eq_mul_inv_direct, show (1 : Rat.Fraction.Rational)⁻¹ = 1 from by decide, mul_one]
    using bound

section
open Purelib.Approximation
open Purelib.Data
/-- The finite per-term allocation is no larger than its nonnegative original budget. -/
private theorem perTerm_le {value : Rat.Fraction.Rational} (nonnegative : 0 ≤ value) (count : Nat) :
    Rational.Budget.Aggregate.perTerm value count ≤ value := by
  unfold Rational.Budget.Aggregate.perTerm
  rw [Rational.Budget.Aggregate.countCoordinate_eq]
  apply divide_le_self nonnegative
  have lower : (1 : Rat.Fraction.Rational) ≤ (count : Rat.Fraction.Rational) + 1 := le_add_of_nonneg_left
    (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
  have square : (1 : Rat.Fraction.Rational) ≤ ((count : Rat.Fraction.Rational) + 1)^2 := by
    simpa only [one_pow] using Rat.Fraction.Order.Arithmetic.pow_le_pow_direct (by
        decide : (0 : Rat.Fraction.Rational) ≤ 1) lower 2
  exact (show (1 : Rat.Fraction.Rational) ≤ 2 by decide).trans
    ((show (2 : Rat.Fraction.Rational) = 2 * 1 by ring1).trans_le
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by
          decide : (0 : Rat.Fraction.Rational) ≤ 2)))

/-- The retained nested all-hole component allocation is no larger than its original target. -/
theorem familyFineComponent_le : allocated.fine.component ≤ target := by
  have perHolePositive : 0 < allocated.perHole := by
    rw [allocated.perHole_eq]
    exact Rational.Budget.Aggregate.perTerm_positive allocated.positive _
  have quarterPositive : 0 < allocated.perHole / 4 := Rat.Fraction.Order.Field.div_pos_direct perHolePositive (by
    decide)
  have innerQuarterPositive : 0 < allocated.perHole / 4 / 4 := Rat.Fraction.Order.Field.div_pos_direct quarterPositive
    (by decide)
  rw [allocated.fine.component_eq]
  apply (perTerm_le innerQuarterPositive.le _).trans
  apply (divide_le_self quarterPositive.le (by decide : (1 : Rat.Fraction.Rational) ≤ 4)).trans
  apply (divide_le_self perHolePositive.le (by decide : (1 : Rat.Fraction.Rational) ≤ 4)).trans
  rw [allocated.perHole_eq]
  exact perTerm_le allocated.positive.le _

end

namespace RemainingBandRequest

variable {floor : Nat} {allowance : Rational}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- The pre-grid target cap pays the retained non-exterior boundary energy.

Use the same allocated family grid, annular request and cached perimeter samples; the squared residual is bounded by
four times the homogeneous allowance, squared. -/
theorem paid (request :
  Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest (grid :=
  allocated.family.single.grid) excision traces floor)
    (later : request.index ≤ stage) (samples : PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank allocated.family.single.grid.faces)
    (positive : 0 < allowance)
    (targetLe : target ≤
      BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) allowance) :
    Data.Gaussian.Norm.Basic.normSq
      (CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors -
      Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors
        (Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision) (centeredSideSum samples)
        .exterior) ≤
      (4 * (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
  have bound := request.accurate later samples neighbors allocated.fine.component_positive.le allocated.fine.band_paid
  exact bound.trans
    (BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget_paid
    positive allocated.fine.component_positive.le
    ((familyFineComponent_le allocated).trans targetLe)
    (Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget.NewtonPreparation.AreaRequest.regulars_count
      allocated.fine.area)
    (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest.holes_count allocated.fine.area) _)

end RemainingBandRequest
end SynchronizedSurfaceRequests
end Purelib.Riemann.RootContinuation.NewtonRemainingBandPayment
