module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

@[expose] public section

/-! Pay the complete ramified source and physical comparison inside the retained raw allowance. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}

section
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- One fifth of the retained raw-energy allowance.

This positive rational target allocates the five source-error contributions for the odd branch case. -/
def rawOddSourceTarget (observations : ProtectedObservations original) : Fraction.Rational :=
  (NewtonRawEnergyBudget.rawEnergyAllowance observations) / 5

/-- The odd source target is strictly positive. -/
theorem rawOddSourceTarget_positive (observations : ProtectedObservations original) :
    0 < (rawOddSourceTarget observations) :=
  Fraction.Order.Field.div_pos_direct (NewtonRawEnergyBudget.rawEnergyAllowance_positive observations)
    (by decide +kernel)

/-- Five odd source targets equal the original raw-energy allowance. -/
theorem rawOddSourceTarget_paid (observations : ProtectedObservations original) :
    5 * (rawOddSourceTarget observations) = (NewtonRawEnergyBudget.rawEnergyAllowance observations) := by
  unfold rawOddSourceTarget
  exact (Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel))

/-- Sixteen times the square of the raw-energy allowance.

This is the squared-norm target for the retained odd physical-boundary comparison. -/
def rawOddPhysicalTarget (observations : ProtectedObservations original) : Fraction.Rational :=
  16 * (NewtonRawEnergyBudget.rawEnergyAllowance observations)^2

/-- The odd physical target is strictly positive. -/
theorem rawOddPhysicalTarget_positive (observations : ProtectedObservations original) :
    0 < (rawOddPhysicalTarget observations) :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) (Fraction.Order.Arithmetic.pow_pos_direct
    (NewtonRawEnergyBudget.rawEnergyAllowance_positive observations) 2)

end

open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- The odd-case error deductions leave the protected surface lower constant.

Replaces the five source targets by their exact common allowance and verifies the remaining original multiplicities
algebraically. -/
theorem rawOddEnergy_paid (observations : ProtectedObservations original) :
    2 * ((NewtonObservationSurfaceLower.surfaceLowerConstant observations) - (NewtonRawEnergyBudget.rawEnergyAllowance
      observations) - (NewtonRawEnergyBudget.rawEnergyAllowance observations) -
      (NewtonRawEnergyBudget.rawEnergyAllowance observations) - (NewtonRawEnergyBudget.rawEnergyAllowance observations))
        - (NewtonRawEnergyBudget.rawEnergyAllowance observations) -
      (NewtonRawEnergyBudget.rawEnergyAllowance observations) - (5 * (rawOddSourceTarget observations) +
        (NewtonRawEnergyBudget.rawEnergyAllowance observations) +
      (NewtonRawEnergyBudget.rawEnergyAllowance observations) + (NewtonRawEnergyBudget.rawEnergyAllowance observations))
        -
      ((NewtonRawEnergyBudget.rawEnergyAllowance observations) + (NewtonRawEnergyBudget.rawEnergyAllowance
        observations)) = (NewtonObservationSurfaceLower.surfaceLowerConstant observations) := by
  rw [(rawOddSourceTarget_paid observations)]
  exact (show _ = 2 * ((NewtonObservationSurfaceLower.surfaceLowerConstant observations) -
    (NewtonRawEnergyBudget.rawEnergyAllowance observations) - (NewtonRawEnergyBudget.rawEnergyAllowance observations) -
      (NewtonRawEnergyBudget.rawEnergyAllowance observations) - (NewtonRawEnergyBudget.rawEnergyAllowance observations))
        - (NewtonRawEnergyBudget.rawEnergyAllowance observations) -
      (NewtonRawEnergyBudget.rawEnergyAllowance observations) - ((NewtonRawEnergyBudget.rawEnergyAllowance observations)
        + (NewtonRawEnergyBudget.rawEnergyAllowance observations) +
      (NewtonRawEnergyBudget.rawEnergyAllowance observations)) - (NewtonRawEnergyBudget.rawEnergyAllowance observations)
        - (NewtonRawEnergyBudget.rawEnergyAllowance observations) -
      (NewtonRawEnergyBudget.rawEnergyAllowance observations) from by ring1).trans
        (NewtonRawEnergyBudget.rawEnergyAllowance_paid observations)

end Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
