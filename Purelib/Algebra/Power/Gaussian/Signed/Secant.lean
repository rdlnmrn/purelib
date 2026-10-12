module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Power.Gaussian.Secant
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Inverse.Subtraction
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
public import Purelib.Data.Int.Exponent

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Defs

open Purelib.Algebra.Field
open Purelib.Algebra.Power.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Int (Exponent)
open Purelib.Data.Rat

section
public section

/-!
# Signed Gaussian power secant kernels

Natural powers and reciprocal positive powers have finite difference kernels
and formal derivatives. At nonzero inputs the kernels factor value differences,
and their diagonal agrees with the derivative. Negative exponents retain the
original nonzero witnesses needed for reciprocal cancellation.
-/

namespace Purelib.Algebra.Power.Gaussian.Signed.Secant

/-- Evaluate a Gaussian power with an explicitly signed exponent.

Nonnegative exponents use natural powers, while a negative exponent uses the total reciprocal of the corresponding
positive power. -/
@[expose] def signedPower (x : Canonical) : Exponent → Canonical
  | .nonnegative degree => x ^ degree
  | .negative predecessor => (x ^ (predecessor + 1))⁻¹

/-- Construct a finite kernel for a difference of signed Gaussian powers.

The negative branch scales the positive-power kernel by the product of the two reciprocal powers and negates it. -/
@[expose] def signedPowerKernel (x y : Canonical) : Exponent → Canonical
  | .nonnegative degree => Secant.powerKernel x y degree
  | .negative predecessor =>
      -(Secant.powerKernel x y (predecessor + 1) *
        ((x ^ (predecessor + 1))⁻¹ * (y ^ (predecessor + 1))⁻¹))

/-- Evaluate the formal derivative of a signed Gaussian power.

The negative branch scales the next reciprocal power by the negative rational magnitude of the exponent. -/
@[expose] def signedPowerDerivative (x : Canonical) : Exponent → Canonical
  | .nonnegative degree => Secant.powerDerivative x degree
  | .negative predecessor =>
      Scale.scale
        (-((predecessor + 1 : Nat) : Fraction.Rational))
        ((x ^ (predecessor + 2))⁻¹)

/-- Factor a difference of signed Gaussian powers at two nonzero inputs.

The explicit nonzero hypotheses justify reciprocal cancellation in the negative branch. -/
theorem signedPower_sub_factor (x y : Canonical)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) : ∀ exponent,
    signedPower x exponent - signedPower y exponent =
      (x - y) * signedPowerKernel x y exponent
  | .nonnegative degree => Secant.power_sub_power_factor x y degree
  | .negative predecessor => by
      let degree := predecessor + 1
      have xPowerNonzero :=
        Power.pow_ne_zero_direct x xNonzero degree
      have yPowerNonzero :=
        Power.pow_ne_zero_direct y yNonzero degree
      rw [signedPower, signedPower, signedPowerKernel]
      calc
        (x ^ degree)⁻¹ - (y ^ degree)⁻¹ =
            -(x ^ degree - y ^ degree) *
              ((x ^ degree)⁻¹ * (y ^ degree)⁻¹) :=
          Inverse.Subtraction.inverse_sub_inverse xPowerNonzero yPowerNonzero
        _ = (-((x - y) * Secant.powerKernel x y degree)) *
              ((x ^ degree)⁻¹ * (y ^ degree)⁻¹) := by
          rw [Secant.power_sub_power_factor x y degree]
        _ = (x - y) *
            (-(Secant.powerKernel x y degree *
              ((x ^ degree)⁻¹ * (y ^ degree)⁻¹))) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im, Basic.mul_re, Basic.mul_im] <;>
            ring1

/-- Reduce the reciprocal product on the diagonal of a negative-power kernel.

For a nonzero Gaussian input, the product of one lower power and two reciprocal successor powers is the reciprocal of
the power two degrees higher. -/
private theorem negative_power_diagonal_algebra (x : Canonical)
    (xNonzero : x ≠ 0) (predecessor : Nat) :
    x ^ predecessor *
        ((x ^ (predecessor + 1))⁻¹ *
          (x ^ (predecessor + 1))⁻¹) =
      (x ^ (predecessor + 2))⁻¹ := by
  have higherNonzero :=
    Power.pow_ne_zero_direct x xNonzero
      (predecessor + 2)
  have currentNonzero :=
    Power.pow_ne_zero_direct x xNonzero
      (predecessor + 1)
  have currentInvMul :
      (x ^ (predecessor + 1))⁻¹ * x ^ (predecessor + 1) = 1 := by
    simpa only [Field.inv_eq] using
      Field.inv_mul
        (x ^ (predecessor + 1)) currentNonzero
  have higherInvMul :
      (x ^ (predecessor + 2))⁻¹ * x ^ (predecessor + 2) = 1 := by
    simpa only [Field.inv_eq] using
      Field.inv_mul
        (x ^ (predecessor + 2)) higherNonzero
  have currentPower :
      x ^ (predecessor + 1) = x ^ predecessor * x := by
    exact pow_succ x predecessor
  have higherPower :
      x ^ (predecessor + 2) = x ^ (predecessor + 1) * x := by
    rw [show predecessor + 2 = (predecessor + 1) + 1 by ring1]
    exact pow_succ x (predecessor + 1)
  apply Field.mul_right_cancel_of_ne higherNonzero
  calc
    (x ^ predecessor *
          ((x ^ (predecessor + 1))⁻¹ *
            (x ^ (predecessor + 1))⁻¹)) *
        x ^ (predecessor + 2) =
      (x ^ (predecessor + 1) * (x ^ (predecessor + 1))⁻¹) *
        ((x ^ (predecessor + 1))⁻¹ *
          x ^ (predecessor + 1)) := by
        rw [higherPower, currentPower]
        ring1
    _ = 1 := by
      rewrite [ExplicitField.mul_inv_cancel _ currentNonzero,
        currentInvMul, Basic.one_mul]
      rfl
    _ = (x ^ (predecessor + 2))⁻¹ *
        x ^ (predecessor + 2) := by
      exact higherInvMul.symm

/-- The signed power kernel on equal nonzero inputs is its formal derivative.

The nonzero hypothesis supplies the cancellations needed by negative exponents. -/
theorem signedPowerKernel_diagonal (x : Canonical) (xNonzero : x ≠ 0) :
    ∀ exponent,
      signedPowerKernel x x exponent = signedPowerDerivative x exponent
  | .nonnegative degree => Secant.powerKernel_diagonal x degree
  | .negative predecessor => by
      rw [signedPowerKernel, signedPowerDerivative,
        Secant.powerKernel_diagonal, Secant.powerDerivative]
      rw [← Scale.scale_mul_product,
        negative_power_diagonal_algebra x xNonzero predecessor]
      rewrite [Nat.cast_succ]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.neg_re, Basic.neg_im] <;> ring1

end Purelib.Algebra.Power.Gaussian.Signed.Secant

end
