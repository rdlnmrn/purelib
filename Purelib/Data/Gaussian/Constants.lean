module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Ring.MinimalAxioms
import Purelib.Tactic.Ring

/-!
# Exact Gaussian constants

The displayed Gaussian pairs give the coordinate-axis units, one half and
one plus i. Their laws use finite coordinate arithmetic and the total
Gaussian reciprocal, including its value at zero.
-/

namespace Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat.Fraction (Rational)

/-- The exact Gaussian rational one plus i. -/
@[expose] public def gamma : Canonical := ⟨1, 1⟩

/-- The squared norm of one plus i is two. -/
public theorem normSq_gamma : Canonical.normSq gamma = 2 := by
  change (1 : Rational) * 1 + 1 * 1 = 2
  ring1

end Purelib.Data.Gaussian.Basic.Canonical

namespace Purelib.Data.Gaussian.Constants

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.Rat.Fraction (Rational)

/-- The exact Gaussian rational minus i. -/
@[expose] public def negativeImaginaryUnit : Canonical := ⟨0, -1⟩

/-- Multiplication by minus i sends the imaginary coordinate to the real coordinate.

The displayed pair has real coordinate zero and imaginary coordinate minus
one, so the Gaussian product reduces to the original imaginary coordinate. -/
public theorem negativeImaginaryUnit_mul_re (point : Canonical) :
    (negativeImaginaryUnit * point).re = point.im := by
  change 0 * point.re - -1 * point.im = point.im
  ring1

/-- Multiplication by minus i preserves Gaussian squared norm.

The product norm is the product of the two original norms, and the displayed
minus-i pair has squared norm one. -/
public theorem normSq_negativeImaginaryUnit_mul (point : Canonical) :
    Norm.Basic.normSq (negativeImaginaryUnit * point) = Norm.Basic.normSq point := by
  rw [Norm.Basic.normSq_mul]
  change ((0 : Rational) ^ 2 + (-1) ^ 2) * Norm.Basic.normSq point = Norm.Basic.normSq point
  ring1

/-- The exact Gaussian rational i. -/
@[expose] public def imaginaryUnit : Canonical := ⟨0, 1⟩

/-- The real Gaussian rational one half. -/
@[expose] public def half : Canonical := ⟨1 / 2, 0⟩

/-- The exact reciprocal of twice i, with imaginary coordinate minus one half. -/
@[expose] public def inverseTwoI : Canonical := ⟨0, -(1 / 2)⟩

/-- A nonzero Gaussian times one plus i times its reciprocal equals one plus i.

Associativity and commutativity place the original nonzero Gaussian next to
its total reciprocal, allowing the supplied nonzero certificate to cancel it. -/
public theorem mul_quotient_eq_gamma (z : Canonical) (nonzero : z ≠ 0) :
    z * (Canonical.gamma * z⁻¹) = Canonical.gamma := by
  rw [← Gaussian.Basic.mul_assoc,
    Gaussian.Basic.mul_comm z Canonical.gamma,
    Gaussian.Basic.mul_assoc,
    Field.inv_eq,
    Field.mul_inv z nonzero,
    Gaussian.Basic.mul_one]

/-- Multiplication of a reciprocal by one plus i divides its coordinate sum and difference by squared norm.

The total Gaussian reciprocal has the original norm denominator in both
coordinates. This identity holds also at zero, without a nonzero hypothesis. -/
public theorem quotient_coordinates (u : Canonical) :
    (Canonical.gamma * u⁻¹).re = (u.re + u.im) / Norm.Basic.normSq u ∧
      (Canonical.gamma * u⁻¹).im = (u.re - u.im) / Norm.Basic.normSq u := by
  constructor
  · calc
      (Canonical.gamma * u⁻¹).re = (Canonical.gamma * Field.inv u).re :=
        congrArg (fun value : Canonical => (Canonical.gamma * value).re) (Field.inv_eq u)
      _ = (u.re + u.im) / Norm.Basic.normSq u := by
        change 1 * (u.re / Norm.Basic.normSq u) -
          1 * (-u.im / Norm.Basic.normSq u) = (u.re + u.im) / Norm.Basic.normSq u
        rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct,
          Rat.Fraction.Field.div_eq_mul_inv_direct,
          Rat.Fraction.Field.div_eq_mul_inv_direct]
        ring1
  · calc
      (Canonical.gamma * u⁻¹).im = (Canonical.gamma * Field.inv u).im :=
        congrArg (fun value : Canonical => (Canonical.gamma * value).im) (Field.inv_eq u)
      _ = (u.re - u.im) / Norm.Basic.normSq u := by
        change 1 * (-u.im / Norm.Basic.normSq u) +
          1 * (u.re / Norm.Basic.normSq u) = (u.re - u.im) / Norm.Basic.normSq u
        rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct,
          Rat.Fraction.Field.div_eq_mul_inv_direct,
          Rat.Fraction.Field.div_eq_mul_inv_direct]
        ring1

/-- The Gaussian value one plus i is nonzero. -/
private theorem gamma_ne : Canonical.gamma ≠ 0 := by decide

/-- Inverting one plus i times the reciprocal of its product with a nonzero Gaussian recovers that Gaussian.

All three reciprocals retain the original Gaussian products. Their supplied
nonzero certificates permit multiplication cancellation without selecting a
new residual or changing either coordinate. -/
public theorem inverse_gamma_inverse_mul
    (residual : Canonical) (residualNonzero : residual ≠ 0) :
    (Canonical.gamma * (Canonical.gamma * residual)⁻¹)⁻¹ = residual := by
  have productNonzero : Canonical.gamma * residual ≠ 0 :=
    Field.mul_ne_zero_direct gamma_ne residualNonzero
  have tailNonzero : (Canonical.gamma * residual)⁻¹ ≠ 0 :=
    Field.inv_ne_zero_direct productNonzero
  have gammaTailNonzero : Canonical.gamma * (Canonical.gamma * residual)⁻¹ ≠ 0 :=
    Field.mul_ne_zero_direct gamma_ne tailNonzero
  apply Field.mul_right_cancel_of_ne gammaTailNonzero
  calc
    (Canonical.gamma * (Canonical.gamma * residual)⁻¹)⁻¹ *
          (Canonical.gamma * (Canonical.gamma * residual)⁻¹) = 1 :=
      Canonical.inv_mul_cancel _ gammaTailNonzero
    _ = residual * (Canonical.gamma * (Canonical.gamma * residual)⁻¹) := by
      calc
        1 = (Canonical.gamma * residual) * (Canonical.gamma * residual)⁻¹ :=
          (Canonical.mul_inv_cancel _ productNonzero).symm
        _ = residual * (Canonical.gamma * (Canonical.gamma * residual)⁻¹) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The squared norm of one plus i is two. -/
@[simp] public theorem normSq_gamma : Norm.Basic.normSq Canonical.gamma = 2 :=
  (Norm.Basic.normSq_eq_canonical Canonical.gamma).trans Canonical.normSq_gamma

/-- The unit Gaussian rational on the positive real axis. -/
@[expose] public def horizontalDirection : Canonical := ⟨1, 0⟩

end Purelib.Data.Gaussian.Constants
