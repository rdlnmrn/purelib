module

public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field

/-!
# Conjugation and explicit Gaussian reciprocals

The original total reciprocal and conjugation retain their same coordinate
operations. Nonzero cancellation and the actual unit-quadrance identity
supply the finite reciprocal transports.
-/

public section

namespace Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.Field

/-- Equality of conjugates identifies their same original structural Gaussian scalars. -/
theorem conj_injective : Function.Injective (conj : Canonical → Canonical) := by
  intro left right equal
  have twice := congrArg conj equal
  rewrite [conj_conj, conj_conj] at twice
  exact twice

/-- Gaussian conjugation commutes with the original total reciprocal, including zero. -/
theorem conj_inv (point : Canonical) : conj point⁻¹ = (conj point)⁻¹ := by
  by_cases zero : point = 0
  · subst point
    exact rfl
  · apply Field.mul_right_cancel_of_ne (conj_ne_zero zero)
    calc
      conj point⁻¹ * conj point = conj (point⁻¹ * point) := (conj_mul _ _).symm
      _ = 1 := congrArg conj (inv_mul_cancel point zero)
      _ = (conj point)⁻¹ * conj point := (inv_mul_cancel _ (conj_ne_zero zero)).symm

/-- Taking the original reciprocal twice returns the supplied nonzero Gaussian scalar. -/
theorem inv_inv_nonzero (point : Canonical) (nonzero : point ≠ 0) : (point⁻¹)⁻¹ = point := by
  apply Field.mul_right_cancel_of_ne (inv_ne_zero nonzero)
  exact (inv_mul_cancel point⁻¹ (inv_ne_zero nonzero)).trans (mul_inv_cancel point nonzero).symm

/-- At unit quadrance the original reciprocal is the same coordinate conjugate. -/
theorem inv_eq_conj_of_normSq_one (point : Canonical) (unit : point.normSq = 1) : point⁻¹ = conj point := by
  apply Canonical.ext
  · change point.re / point.normSq = point.re
    rewrite [unit]
    change _ * ((1 : Fraction.Rational)⁻¹) = _
    rewrite [show ((1 : Fraction.Rational)⁻¹) = 1 by decide +kernel]
    exact Fraction.Field.mul_one_direct _
  · change -point.im / point.normSq = -point.im
    rewrite [unit]
    change _ * ((1 : Fraction.Rational)⁻¹) = _
    rewrite [show ((1 : Fraction.Rational)⁻¹) = 1 by decide +kernel]
    exact Fraction.Field.mul_one_direct _

end Purelib.Data.Gaussian.Basic.Canonical

end
