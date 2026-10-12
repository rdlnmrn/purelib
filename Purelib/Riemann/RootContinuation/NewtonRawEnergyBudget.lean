module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A coefficient-independent allocation for every loss in the regular raw
energy comparison. The sixteen weighted losses leave the observation margin. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}

section
open Purelib.Data.Rat
open Purelib.Riemann.Topology
/-- One sixteenth of the protected surface lower constant.

This rational allowance is the common scale for the individual raw-energy error terms. -/
@[expose] def rawEnergyAllowance (observations : ProtectedObservations original) : Fraction.Rational :=
  (NewtonObservationSurfaceLower.surfaceLowerConstant observations) / 16

/-- The raw-energy allowance is strictly positive.

Divides the positive protected surface lower constant by sixteen. -/
theorem rawEnergyAllowance_positive (observations : ProtectedObservations original) :
    0 < (rawEnergyAllowance observations) :=
  Fraction.Order.Field.div_pos_direct (NewtonObservationSurfaceLower.surfaceLowerConstant_positive observations) (by
    decide +kernel)

/-- The retained raw-energy deductions leave the surface lower constant.

Expands the common sixteenth allowance and verifies the exact multiplicities of the four doubled terms and eight further
deductions. -/
theorem rawEnergyAllowance_paid (observations : ProtectedObservations original) :
    2 * ((NewtonObservationSurfaceLower.surfaceLowerConstant observations) - (rawEnergyAllowance observations) -
      (rawEnergyAllowance observations) -
      (rawEnergyAllowance observations) - (rawEnergyAllowance observations)) - (rawEnergyAllowance observations) -
      (rawEnergyAllowance observations) - ((rawEnergyAllowance observations) + (rawEnergyAllowance observations) +
      (rawEnergyAllowance observations)) - (rawEnergyAllowance observations) - (rawEnergyAllowance observations) -
      (rawEnergyAllowance observations) = (NewtonObservationSurfaceLower.surfaceLowerConstant observations) := by
  unfold rawEnergyAllowance
  calc
    _ = 2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations) -
      (NewtonObservationSurfaceLower.surfaceLowerConstant observations) / 16 * 16 := by
      ring1
    _ = (NewtonObservationSurfaceLower.surfaceLowerConstant observations) := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)]; ring1

end

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests
  (remainingBoundaryTarget remainingBoundaryTarget_positive)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- Shared annular and remaining-boundary target for the raw-energy grid.

Takes the smaller of the annular energy allowance divided by eighty-two quarters and the remaining-boundary target at
the retained outer count. -/
@[expose] def rawEnergyGridTarget (observations : ProtectedObservations original) (count : Nat) : Fraction.Rational :=
  min (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations)
    / (82 / 4))
    (Meshes.Newton.Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus count (rawEnergyAllowance observations))

/-- The shared raw-energy grid target is positive.

Both terms of the minimum are positive for the protected surface allowance. -/
theorem rawEnergyGridTarget_positive (observations : ProtectedObservations original) (count : Nat) :
    0 < (rawEnergyGridTarget observations) count :=
  Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive (rawEnergyAllowance_positive
    observations))
    (Fraction.Order.Field.div_pos_direct (by decide +kernel) (by decide +kernel)))

      (BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget_positive
      (rawEnergyAllowance_positive observations))

/-- The grid target pays the scaled annular allowance.

Multiplying the selected target by eighty-two quarters stays within the conjugate-request energy allowance. -/
theorem rawEnergyGridTarget_annular (observations : ProtectedObservations original) (count : Nat) :
    (82 / 4 : Fraction.Rational) * (rawEnergyGridTarget observations) count ≤
      Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations)
        := by
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.min_le_left
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations) /
      (82 / 4))
    (Meshes.Newton.Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus count (rawEnergyAllowance observations))) ((Fraction.Order.Field.div_pos_direct (by
          decide +kernel : (0 : Fraction.Rational) < 82) (by decide +kernel : (0 : Fraction.Rational) < 4)).le)
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt (Fraction.Order.Field.div_pos_direct (by decide +kernel) (by
    decide +kernel)))] at bound
  exact (Fraction.Field.mul_comm _ _).trans_le bound

end

open Purelib.Curves.Hyperelliptic in
/-- The grid target is below the retained remaining-boundary target.

This is the second inequality supplied by its defining minimum. -/
theorem rawEnergyGridTarget_remaining (observations : ProtectedObservations original) (count : Nat) :
    (rawEnergyGridTarget observations) count ≤
      Meshes.Newton.Complement.BoundaryBudget.ProtectedObservations.SynchronizedSurfaceRequests.remainingBoundaryTarget
      genus count (rawEnergyAllowance observations) :=
  Fraction.Order.Basic.min_le_right _ _

end Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
