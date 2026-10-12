module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Defs

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Rat

section
public section

/-!
# Gaussian power secant kernels and formal derivatives

The finite secant kernel factors the difference of equal-degree nonnegative
Gaussian powers. Its diagonal is the formal derivative computed by scaling the
preceding power by the degree. Both constructions use structural recursion on
the finite degree.
-/

namespace Purelib.Algebra.Power.Gaussian.Secant

/-- Construct the finite divided-difference kernel of a nonnegative power.

Recursion uses zero at degree zero and adds the next power of the first argument to the second argument times the
previous kernel. -/
@[expose] def powerKernel (x y : Canonical) : Nat → Canonical
  | 0 => 0
  | degree + 1 => x ^ degree + y * powerKernel x y degree

/-- The power kernel at degree zero is zero. -/
@[simp] theorem powerKernel_zero (x y : Canonical) :
    powerKernel x y 0 = 0 := rfl

/-- The successor power kernel adds a power to the scaled previous kernel. -/
@[simp] theorem powerKernel_succ (x y : Canonical) (degree : Nat) :
    powerKernel x y (degree + 1) =
      x ^ degree + y * powerKernel x y degree := rfl

/-- Factor the difference of equal-degree Gaussian powers.

The finite kernel multiplies the difference of the inputs, including when the inputs coincide; no division is performed.
-/
theorem power_sub_power_factor (x y : Canonical) : ∀ degree,
    x ^ degree - y ^ degree = (x - y) * powerKernel x y degree
  | 0 => by
      rewrite [pow_zero, pow_zero, Basic.sub_self, powerKernel_zero, Basic.mul_zero]
      rfl
  | degree + 1 => by
      rw [pow_succ, pow_succ, powerKernel_succ]
      calc
        x ^ degree * x - y ^ degree * y =
            (x - y) * x ^ degree + y * (x ^ degree - y ^ degree) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;>
            ring1
        _ = (x - y) * x ^ degree +
            y * ((x - y) * powerKernel x y degree) := by
          rw [power_sub_power_factor x y degree]
        _ = (x - y) * (x ^ degree + y * powerKernel x y degree) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;>
            ring1

/-- Compute the formal derivative of one nonnegative Gaussian power.

Degree zero gives zero; a positive degree scales the preceding power by its rational degree. -/
@[expose] def powerDerivative (x : Canonical) : Nat → Canonical
  | 0 => 0
  | degree + 1 =>
      Scale.scale (degree + 1 : Fraction.Rational) (x ^ degree)

/-- The derivative values satisfy a first-order power recurrence.

For each degree, the next derivative is the current power plus the input times the current derivative. -/
private theorem powerDerivative_succ_identity (x : Canonical) : ∀ degree,
    powerDerivative x (degree + 1) =
      x ^ degree + x * powerDerivative x degree
  | 0 => by
      simp only [powerDerivative, pow_zero, Basic.mul_zero,
        _root_.add_zero]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.one_re, Basic.one_im] <;> ring1
  | degree + 1 => by
      simp only [powerDerivative, pow_succ]
      rewrite [Nat.cast_succ]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.add_re, Basic.add_im, Basic.mul_re,
          Basic.mul_im] <;> ring1

/-- The power kernel on equal inputs is the formal power derivative.

The identity holds at every finite nonnegative degree, including zero. -/
theorem powerKernel_diagonal (x : Canonical) : ∀ degree,
    powerKernel x x degree = powerDerivative x degree
  | 0 => rfl
  | degree + 1 => by
      rw [powerKernel_succ, powerKernel_diagonal,
        powerDerivative_succ_identity]

end Purelib.Algebra.Power.Gaussian.Secant

end
