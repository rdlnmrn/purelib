module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A coefficient-independent contact budget pays the global centered error.
The resulting energy bound retains every physical and outer-corner term. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ConjugateRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_positive energyAllowanceTarget_paid)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests (GlobalEnergyRequest)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
open Purelib.Riemann.RootContinuation.NewtonGlobalCornerBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (cornerBoundary exterior_eq_corner_boundary)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples (paired exterior
  physical)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  mul_le_mul_of_nonneg_right_direct)

namespace SynchronizedSurfaceRequests

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Per-contact target paying a global contact allowance.

Divides the genus energy target by four times one plus the fourth power of the regular-face count. -/
@[expose] def contactTarget (genus faces : Nat) (allowance : Fraction.Rational) : Fraction.Rational :=
  Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance /
    (4 * ((Budget.Aggregate.countCoordinate faces) ^ 4 + 1))

section
open Purelib.Data.Rat
/-- The fourth power of a rational natural-number cast is nonnegative. -/
private theorem fourth_nonnegative (faces : Nat) : 0 ≤ (faces : Fraction.Rational) ^ 4 :=
  (Fraction.Order.Arithmetic.sq_nonneg_direct ((faces : Fraction.Rational) ^ 2)).trans_eq (by ring1)

/-- The contact-target denominator is strictly positive.

The fourth-power term is nonnegative and the added one keeps the denominator positive even for an empty face list. -/
private theorem contact_denominator_positive (faces : Nat) : 0 < (4 : Fraction.Rational) * ((faces : Fraction.Rational)
  ^ 4 + 1) :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (fourth_nonnegative faces) (by decide))

end

section
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- A positive contact allowance gives a positive local target.

Uses positivity of the genus energy target and the fourth-power denominator. -/
theorem contactTarget_positive {genus faces : Nat} {allowance : Fraction.Rational} (positive : 0 < allowance) :
    0 < contactTarget genus faces allowance := by
  unfold contactTarget
  rw [Budget.Aggregate.countCoordinate_eq]
  exact Fraction.Order.Field.div_pos_direct
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive positive)
    (contact_denominator_positive faces)

/-- The local contact target pays four times the face-count fourth power.

The added one in the denominator leaves the scaled contact sum below the original genus energy target. -/
theorem contactTarget_paid {genus faces : Nat} {allowance : Fraction.Rational} (positive : 0 < allowance) :
    4 * (faces : Fraction.Rational) ^ 4 * contactTarget genus faces allowance ≤
      Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance := by
  have product : (4 * ((faces : Fraction.Rational) ^ 4 + 1)) * contactTarget genus faces allowance =
      Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance := by
    unfold contactTarget
    rw [Budget.Aggregate.countCoordinate_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (contact_denominator_positive faces).ne'
  have factor : (4 : Fraction.Rational) * (faces : Fraction.Rational) ^ 4 ≤ 4 * ((faces : Fraction.Rational) ^ 4 + 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (le_add_of_nonneg_right (by decide)) (by decide)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factor (contactTarget_positive
    positive).le).trans_eq product

end

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Pay the total paired-centered error from horizontal and vertical contact bounds.

Combines the retained matching-side estimates with the fourth-power count payment and genus energy allowance, preserving
the coefficient-norm square. -/
theorem contact_paid {allowance : Fraction.Rational} (positive : 0 < allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (centeredSideSum samples .top first - centeredSideSum samples .bottom last) ≤
        (genus : Fraction.Rational) ^ 2 * coefficientNormSq coefficients ^ 2 * contactTarget genus
          grid.faces.regulars.length allowance)
    (vertical : ∀ first last, GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (centeredSideSum samples .right first - centeredSideSum samples .left last) ≤
        (genus : Fraction.Rational) ^ 2 * coefficientNormSq coefficients ^ 2 * contactTarget genus
          grid.faces.regulars.length allowance) :
    Data.Gaussian.Norm.Basic.normSq (pairedCentered samples) ≤ (4 * (allowance * coefficientNormSq coefficients)) ^ 2
      := by
  have bound := paired_error_bound samples
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (contactTarget_positive positive).le) horizontal vertical
  have equal : samples.paired - pairedEndpoints samples = pairedCentered samples := by
    rw [paired_decomposition samples]
    ring1
  rw [equal] at bound
  apply bound.trans
  calc
    _ = ((genus : Fraction.Rational) ^ 2 *
        (4 * (grid.faces.regulars.length : Fraction.Rational) ^ 4 * contactTarget genus grid.faces.regulars.length
          allowance)) *
          coefficientNormSq coefficients ^ 2 := by ring1
    _ ≤ ((genus : Fraction.Rational) ^ 2 * Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget
      genus allowance) * coefficientNormSq coefficients ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (contactTarget_paid positive)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ ≤ (4 * allowance) ^ 2 * coefficientNormSq coefficients ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid positive)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = _ := by ring1

end PerimeterSamples

namespace GlobalEnergyRequest

variable {depth : Nat}
  {requests : SynchronizedSurfaceRequests (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {ownershipAllowance exteriorAllowance faceAllowance contactAllowance : Rational}

open Purelib in
open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Topology in
/-- Subtract the paid contact allowance from the global energy lower bound.

Uses the exact corner-and-physical decomposition and paired-centered error certificate to retain a coercive lower bound
after contact removal. -/
theorem energy_lower_after_contacts
    (request : GlobalEnergyRequest requests ownershipAllowance exteriorAllowance faceAllowance)
    (later : request.index ≤ stage)
    (readings : Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Topology.BranchedCover.Double.Attachment.Face)
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    {traces : PerimeterTraces requests} (samples : PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (positive : 0 < contactAllowance)
    (contacts : Data.Gaussian.Norm.Basic.normSq (pairedCentered samples) ≤ (4 * (contactAllowance * coefficientNormSq
      coefficients)) ^ 2) :
    (2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) - contactAllowance) *
      coefficientNormSq coefficients ≤
        (cornerBoundary faces + physicalCentered samples neighbors).im / 4 := by
  have normNonnegative : 0 ≤ coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Norm.Basic.normSq_nonneg (coefficients row))
    have same := FiniteSum.Fin.sumFin_congr
      (fun row : Fin genus => Norm.Basic.normSq_eq_canonical (coefficients row))
    change 0 ≤ FiniteSum.Fin.sumFin (fun row => (coefficients row).normSq)
    rw [← same]
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have difference : samples.exterior - (cornerBoundary faces + physicalCentered samples neighbors) =
      pairedCentered samples := by
    rw [exterior_eq_corner_boundary samples faces neighbors]
    ring1
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le samples.exterior
    (cornerBoundary faces + physicalCentered samples neighbors)
    (contactAllowance * coefficientNormSq coefficients) (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le
      normNonnegative)
    (difference ▸ contacts)
  have lower := request.energy_lower later readings observationFace faces samples neighbors
  rw [← samples.exterior_eq_paired_add_physical neighbors] at lower
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := contactAllowance * coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end GlobalEnergyRequest
end SynchronizedSurfaceRequests
end Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
