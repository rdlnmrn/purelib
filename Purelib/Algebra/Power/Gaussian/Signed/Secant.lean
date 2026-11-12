module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Power.Gaussian.Secant
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Conjugate.Arithmetic
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

namespace Purelib.Algebra.Power.Gaussian.Signed.Secant

/-- A sufficient polynomializing shift clears the original signed power.

A displayed negative exponent retains its supplied nonzero-input certificate;
nonnegative exponents also allow zero as an evaluation point. -/
public theorem signedPower_shift (point : Canonical) (exponent : Exponent)
    (shift : Nat) (sufficient : exponent.negativeMagnitude ≤ shift)
    (defined : exponent.negativeMagnitude ≠ 0 → point ≠ 0) :
    point ^ shift * signedPower point exponent = point ^ (exponent.shifted shift) := by
  cases exponent with
  | nonnegative degree => exact (pow_add point shift degree).symm
  | negative predecessor =>
      change predecessor + 1 ≤ shift at sufficient
      have nonzero : point ≠ 0 := defined (Nat.succ_ne_zero predecessor)
      have powerNonzero := Power.pow_ne_zero_direct point nonzero (predecessor + 1)
      change point ^ shift * (point ^ (predecessor + 1))⁻¹ =
        point ^ (shift - (predecessor + 1))
      calc
        point ^ shift * (point ^ (predecessor + 1))⁻¹ =
            (point ^ (shift - (predecessor + 1)) * point ^ (predecessor + 1)) *
              (point ^ (predecessor + 1))⁻¹ := by
          exact congrArg (fun value : Canonical => value * (point ^ (predecessor + 1))⁻¹)
            ((congrArg (fun degree : Nat => point ^ degree)
              (Nat.sub_add_cancel sufficient)).symm.trans
                (pow_add point (shift - (predecessor + 1)) (predecessor + 1)))
        _ = point ^ (shift - (predecessor + 1)) := by
          rewrite [Basic.mul_assoc, ExplicitField.mul_inv_cancel _ powerNonzero, Basic.mul_one]
          exact Eq.refl _

end Purelib.Algebra.Power.Gaussian.Signed.Secant

namespace Purelib.Algebra.Power.Gaussian.Signed.Secant

/-- The original negative magnitude makes the retained signed integer exponent nonnegative. -/
private theorem value_add_negativeMagnitude_nonnegative (exponent : Exponent) :
    0 ≤ exponent.value + (exponent.negativeMagnitude : Int) := by
  cases exponent with
  | nonnegative degree => change 0 ≤ (degree : Int) + (0 : Nat); omega0
  | negative predecessor => change 0 ≤ Int.negSucc predecessor + ((predecessor + 1 : Nat) : Int); omega0

/-- Signed-power multiplication at a nonzero point follows the original exponent addition. -/
private theorem signedPower_add_nonzero (point : Canonical) (nonzero : point ≠ 0)
    (left right : Exponent) :
    signedPower point (Exponent.add left right) = signedPower point left * signedPower point right := by
  let combined := Exponent.add left right
  let shift := left.negativeMagnitude + right.negativeMagnitude
  have combinedValue : combined.value = left.value + right.value := Exponent.add_value left right
  have sufficient : combined.negativeMagnitude ≤ shift := by
    have leftLower := value_add_negativeMagnitude_nonnegative left
    have rightLower := value_add_negativeMagnitude_nonnegative right
    cases shape : combined with
    | nonnegative degree => exact Nat.zero_le _
    | negative predecessor =>
        rewrite [shape] at combinedValue
        change Int.negSucc predecessor = left.value + right.value at combinedValue
        change predecessor + 1 ≤ left.negativeMagnitude + right.negativeMagnitude
        omega0
  have leftDegree := left.shifted_value left.negativeMagnitude (Nat.le_refl _)
  have rightDegree := right.shifted_value right.negativeMagnitude (Nat.le_refl _)
  have combinedDegree := combined.shifted_value shift sufficient
  have degreeEqual : combined.shifted shift =
      left.shifted left.negativeMagnitude + right.shifted right.negativeMagnitude := by
    dsimp only [shift] at combinedDegree
    change combined.shifted (left.negativeMagnitude + right.negativeMagnitude) = _
    omega0
  have leftPower := signedPower_shift point left left.negativeMagnitude (Nat.le_refl _) (fun _ => nonzero)
  have rightPower := signedPower_shift point right right.negativeMagnitude (Nat.le_refl _) (fun _ => nonzero)
  have combinedPower := signedPower_shift point combined shift sufficient (fun _ => nonzero)
  apply Field.mul_right_cancel_of_ne (Power.pow_ne_zero_direct point nonzero shift)
  calc
    signedPower point combined * point ^ shift = point ^ combined.shifted shift :=
      (Basic.mul_comm _ _).trans combinedPower
    _ = point ^ (left.shifted left.negativeMagnitude + right.shifted right.negativeMagnitude) :=
      congrArg (fun exponent : Nat => point ^ exponent) degreeEqual
    _ = (point ^ left.negativeMagnitude * signedPower point left) *
        (point ^ right.negativeMagnitude * signedPower point right) := by
      rewrite [pow_add, leftPower, rightPower]
      exact Eq.refl _
    _ = (signedPower point left * signedPower point right) * point ^ shift := by
      change _ = (signedPower point left * signedPower point right) *
        point ^ (left.negativeMagnitude + right.negativeMagnitude)
      rewrite [pow_add]
      ring1

/-- Signed powers multiply on the common original guarded domain.

The zero-input case is allowed only when both original exponents are
nonnegative. Cancellation in their sum does not erase either source guard. -/
public theorem signedPower_add (point : Canonical) (left right : Exponent)
    (leftDefined : left.negativeMagnitude ≠ 0 → point ≠ 0)
    (rightDefined : right.negativeMagnitude ≠ 0 → point ≠ 0) :
    signedPower point (Exponent.add left right) = signedPower point left * signedPower point right := by
  by_cases pointZero : point = 0
  · cases left with
    | negative predecessor => exact (leftDefined (Nat.succ_ne_zero predecessor) pointZero).elim
    | nonnegative leftDegree =>
        cases right with
        | negative predecessor => exact (rightDefined (Nat.succ_ne_zero predecessor) pointZero).elim
        | nonnegative rightDegree =>
            change point ^ (leftDegree + rightDegree) = point ^ leftDegree * point ^ rightDegree
            exact pow_add point leftDegree rightDegree
  · exact signedPower_add_nonzero point pointZero left right

end Purelib.Algebra.Power.Gaussian.Signed.Secant

public section

namespace Purelib.Algebra.Power.Gaussian.Signed.Secant

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Int (Exponent)
open Purelib.Algebra.Field

/-- Reversing the signed exponent is evaluation at the reciprocal on its original nonzero domain. -/
theorem signedPower_neg (point : Canonical) (nonzero : point ≠ 0) (exponent : Exponent) :
    signedPower point exponent.neg = signedPower point⁻¹ exponent := by
  cases exponent with
  | nonnegative degree =>
      cases degree with
      | zero => rfl
      | succ degree => exact ExplicitField.inverse_pow_nonzero nonzero (degree + 1)
  | negative predecessor =>
      change point ^ (predecessor + 1) = (point⁻¹ ^ (predecessor + 1))⁻¹
      rewrite [← ExplicitField.inverse_pow_nonzero nonzero]
      exact (Canonical.inv_inv_nonzero _ (ExplicitField.pow_ne_zero_of_ne_zero nonzero _)).symm

/-- Gaussian conjugation preserves the same finite signed-power evaluator. -/
theorem signedPower_conj (point : Canonical) (exponent : Exponent) :
    Canonical.conj (signedPower point exponent) = signedPower (Canonical.conj point) exponent := by
  cases exponent with
  | nonnegative degree => exact Power.conj_pow point degree
  | negative predecessor =>
      change Canonical.conj ((point ^ (predecessor + 1))⁻¹) = _
      rewrite [Canonical.conj_inv]
      exact congrArg Inv.inv (Power.conj_pow point (predecessor + 1))

end Purelib.Algebra.Power.Gaussian.Signed.Secant

end
