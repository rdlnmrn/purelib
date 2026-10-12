module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Gamma power and inverse-power transports

The finite Gaussian power recurrence retains gamma and its nonzero inverse.
Their norm and scalar cancellation certificates hold at every natural exponent.
-/

namespace Purelib.Data.Gaussian.Power.Gamma

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- The squared norm of inverse gamma to a natural power is the inverse corresponding power of two.

Gamma is nonzero and has squared norm two. The same retained Gaussian power and inverse operations transport these
scalar certificates for every natural exponent. -/
public theorem normSq_natPow_gamma_inv (count : Nat) :
    Norm.Basic.normSq ((Power.natPow Basic.Canonical.gamma count)⁻¹) = ((2 : Fraction.Rational) ^ count)⁻¹ :=
      by
  have powerNonzero : Power.natPow Basic.Canonical.gamma count ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) count
  rw [Field.inv_eq, Field.normSq_inv _ powerNonzero, Power.normSq_natPow, Constants.normSq_gamma]

/-- A successor gamma power cancels one inverse-gamma factor on a Gaussian value.

The same finite power recurrence and gamma inverse certificate move the supplied Gaussian value between the two retained
scalar products. -/
public theorem regularUnary_value (count : Nat) (value : Basic.Canonical) :
    Power.natPow Basic.Canonical.gamma (count + 1) * (Basic.Canonical.gamma⁻¹ * value) =
      Power.natPow Basic.Canonical.gamma count * value := by
  have cancellation : Basic.Canonical.gamma * Basic.Canonical.gamma⁻¹ = 1 :=
    Basic.Canonical.mul_inv_cancel Basic.Canonical.gamma Constants.Inverse.gamma_ne
  rw [Power.natPow_succ]
  calc
    Power.natPow Basic.Canonical.gamma count * Basic.Canonical.gamma * (Basic.Canonical.gamma⁻¹ * value) =
        Power.natPow Basic.Canonical.gamma count * (Basic.Canonical.gamma * Basic.Canonical.gamma⁻¹) * value := by
      apply Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im] <;> ring1
    _ = Power.natPow Basic.Canonical.gamma count * value := by
      rw [cancellation, Basic.mul_one]

/-- An inverse successor gamma power cancels one gamma factor on a Gaussian value.

Both retained powers are nonzero. Multiplication by the same successor power and the two original inverse cancellation
certificates give the stated scalar transport. -/
public theorem lowUnary_value (count : Nat) (value : Basic.Canonical) :
    (Power.natPow Basic.Canonical.gamma (count + 1))⁻¹ * (Basic.Canonical.gamma * value) =
      (Power.natPow Basic.Canonical.gamma count)⁻¹ * value := by
  let power := Power.natPow Basic.Canonical.gamma count
  let nextPower := Power.natPow Basic.Canonical.gamma (count + 1)
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne count
  have nextPowerNonzero : nextPower ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne (count + 1)
  apply Field.mul_right_cancel_of_ne
    nextPowerNonzero
  have nextIdentity : nextPower = power * Basic.Canonical.gamma := by
    exact Power.natPow_succ Basic.Canonical.gamma count
  have nextCancellation : nextPower⁻¹ * nextPower = 1 :=
    Basic.Canonical.inv_mul_cancel
      nextPower nextPowerNonzero
  have powerCancellation : power⁻¹ * power = 1 :=
    Basic.Canonical.inv_mul_cancel power powerNonzero
  calc
    (nextPower⁻¹ * (Basic.Canonical.gamma * value)) * nextPower = Basic.Canonical.gamma * value := by
      rw [show nextPower⁻¹ * (Basic.Canonical.gamma * value) * nextPower =
          (nextPower⁻¹ * nextPower) * (Basic.Canonical.gamma * value) by
        apply Basic.ext <;>
          simp only [Basic.mul_re, Basic.mul_im] <;> ring1,
        nextCancellation, _root_.one_mul]
    _ = (power⁻¹ * value) * nextPower := by
      rw [nextIdentity]
      calc
        Basic.Canonical.gamma * value = value * Basic.Canonical.gamma :=
          Basic.mul_comm _ _
        _ = (power⁻¹ * power) * (value * Basic.Canonical.gamma) := by
          rw [powerCancellation,
            _root_.one_mul]
        _ = (power⁻¹ * value) * (power * Basic.Canonical.gamma) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im] <;> ring1

end Purelib.Data.Gaussian.Power.Gamma
