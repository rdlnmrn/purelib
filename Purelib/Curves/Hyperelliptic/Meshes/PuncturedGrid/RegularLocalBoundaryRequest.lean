module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

public section

/-! One requested homogeneous error selects spatial energy meshes and then
ownership accuracy, before the shared numerical stage is chosen. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann
open Purelib.RootIsolation

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}

set_option genInjectivity false in
/-- A shared request retaining the energy and clipping-ownership allowances for the original regular local boundary
comparison. -/
structure LocalBoundaryRequest (coarse : (sheet : Fin 2) →
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (target : Fraction.Rational) where
  /-- The positive energy allowance on the original local boundary data. -/ energyTarget : Fraction.Rational
  /-- The energy allowance is the retained minimum of one and the prescribed half-target allocation. -/ energyTarget_eq
    : energyTarget = min 1 (Rational.Budget.Weighted.allowance (target / 2) 128)
  /-- The allowance for the actual clipped ownership comparison. -/ ownershipTarget : Fraction.Rational
  /-- The ownership allowance is the prescribed half-target allocation with the original genus factor. -/
    ownershipTarget_eq : ownershipTarget = Rational.Budget.Weighted.allowance (target / 2) (2 * (genus :
    Fraction.Rational) ^ 2)
  /-- The original energy and ownership contributions together fit the supplied target. -/ paid : 128 * energyTarget ^ 2
    + 2 * (genus : Fraction.Rational) ^ 2 * ownershipTarget ≤ target
  /-- The actual two-sheet energy request at the retained energy allowance. -/ energy :
    Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed energyTarget
  /-- The original clipped ownership request at the retained ownership allowance. -/ ownership :
    Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest energy ownershipTarget

constructive_injectivity LocalBoundaryRequest

namespace LocalBoundaryRequest

variable {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- Allocate the original target between energy and ownership, then retain both actual requests and their paid bound. -/
@[expose] def build (coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
  domains sheet)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed target := by
  let half := target / 2
  have halfPositive : 0 < half := Fraction.Order.Field.div_pos_direct positive (by decide)
  let energyTarget := min 1 (Rational.Budget.Weighted.allowance half 128)
  have energyPositive : 0 < energyTarget := Fraction.Order.Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive halfPositive (by decide +kernel))
  have square : energyTarget ^ 2 ≤ energyTarget := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (show energyTarget ≤ 1 from Fraction.Order.Basic.min_le_left _ _) energyPositive.le
    exact (show energyTarget ^ 2 = energyTarget * energyTarget by ring1).le.trans
      (bound.trans_eq (by ring1))
  have energyPaid : 128 * energyTarget ^ 2 ≤ half :=
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by decide +kernel)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
        (by decide +kernel))).trans
      (Rational.Budget.Weighted.mul_allowance_le halfPositive.le (by decide +kernel))
  let weight := 2 * (Rational.Budget.Aggregate.countCoordinate genus) ^ 2
  have weightEq : weight = 2 * (genus : Fraction.Rational) ^ 2 := by
    dsimp only [weight, -eq_self, -iff_self]
    rw [Rational.Budget.Aggregate.countCoordinate_eq]
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let ownershipTarget := Rational.Budget.Weighted.allowance half weight
  have ownershipPositive : 0 < ownershipTarget := Rational.Budget.Weighted.allowance_positive halfPositive
    weightNonnegative
  have ownershipPaid : weight * ownershipTarget ≤ half := Rational.Budget.Weighted.mul_allowance_le halfPositive.le
    weightNonnegative
  have paid : 128 * energyTarget ^ 2 + 2 * (genus : Fraction.Rational) ^ 2 * ownershipTarget ≤ target := by
    rw [← weightEq]
    exact (add_le_add energyPaid ownershipPaid).trans_eq (by
      change target / 2 + target / 2 = target
      calc
        _ = target / 2 * 2 := by ring1
        _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let energy := Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.build
    coarse fixed energyTarget energyPositive
  exact ⟨energyTarget, rfl, ownershipTarget, by dsimp only [ownershipTarget, half, -eq_self, -iff_self]; rw [weightEq],
    paid, energy, Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest.build energy ownershipTarget
      ownershipPositive⟩

/-- The original local boundary comparison is bounded by the product of coefficient norms and the requested target. -/
theorem bound (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse
  fixed target) {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage}
    (later : request.ownership.index ≤ stage)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples request.energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position :
      Fin faces.length =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary (energy := request.energy) cache left
        right sheet position))) ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Readings.PreparedObservationCoercivity.coefficientNormSq right * target := by
  have nonnegative (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      (fun row => Gaussian.Basic.Canonical.normSq (coefficients row)) (fun row => Gaussian.Basic.Canonical.normSq_nonneg
        (coefficients row))
    simpa only [FiniteSum.Fin.sumFin_zero, Readings.PreparedObservationCoercivity.coefficientNormSq, -eq_self,
      -iff_self] using estimate
  exact (Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary_bound
    request.ownership later samples left right).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.paid
      (Fraction.Order.Arithmetic.mul_nonneg_direct (nonnegative left) (nonnegative right)))

end LocalBoundaryRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
