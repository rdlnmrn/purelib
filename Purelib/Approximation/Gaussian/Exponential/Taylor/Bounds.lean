module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Taylor
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Bounds.ReciprocalNatural
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Bounds

/-! ## Explicit high-degree remainder bounds -/

/-- On the rational unit disk, an exponential Horner monomial starting at denominator at least two has squared norm
bounded by the matching quarter-power. -/
theorem hornerTerm_normSq_le_quarter_pow {x :
  Data.Gaussian.Basic.Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1) :
    ∀ (degree denominator : Nat), 2 ≤ denominator →
      Data.Gaussian.Norm.Basic.normSq (Taylor.Basic.hornerTerm x denominator degree) ≤
        (1 / 4 : Fraction.Rational) ^ degree
  | 0, denominator, atLeastTwo => by
      rw [Taylor.Basic.hornerTerm_zero, Data.Gaussian.Norm.Basic.normSq_one, pow_zero]
  | degree + 1, denominator, atLeastTwo => by
      rw [Taylor.Basic.hornerTerm_succ, Scale.normSq_scale, Data.Gaussian.Norm.Basic.normSq_mul,
        pow_succ]
      have reciprocal :=
        Bounds.ReciprocalNatural.reciprocal_nat_sq_le_quarter atLeastTwo
      have tail := hornerTerm_normSq_le_quarter_pow unitInput
        degree
        (denominator + 1) (by omega)
      have inner :
          Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq (Taylor.Basic.hornerTerm
            x (denominator + 1) degree) ≤
            1 * (1 / 4 : Fraction.Rational) ^ degree :=
        Fraction.Order.Arithmetic.mul_le_mul_direct unitInput tail
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
      calc
        (1 / (denominator : Fraction.Rational)) ^ 2 *
            (Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq
              (Taylor.Basic.hornerTerm x (denominator + 1) degree)) ≤
          (1 / 4 : Fraction.Rational) *
            (1 * (1 / 4 : Fraction.Rational) ^ degree) :=
          Fraction.Order.Arithmetic.mul_le_mul_direct reciprocal inner
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Data.Gaussian.Norm.Basic.normSq_nonneg x) (Data.Gaussian.Norm.Basic.normSq_nonneg _))
            (by decide)
        _ = (1 / 4 : Fraction.Rational) ^ degree * (1 / 4) := by ring1

/-- On the rational unit disk, the next Taylor monomial has squared norm bounded by the quarter-power at the preceding
degree. -/
theorem taylorTerm_succ_normSq_le {x :
  Data.Gaussian.Basic.Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (degree : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Taylor.Basic.taylorTerm x (degree + 1)) ≤
      (1 / 4 : Fraction.Rational) ^ degree := by
  rw [← Taylor.hornerTerm_one_eq_taylorTerm, Taylor.Basic.hornerTerm_succ,
    Scale.normSq_scale, Data.Gaussian.Norm.Basic.normSq_mul]
  have scalar : (1 / ((1 : Nat) : Fraction.Rational)) ^ 2 = 1 := by decide
  rw [scalar, Fraction.Field.one_mul]
  have tail := hornerTerm_normSq_le_quarter_pow unitInput degree 2 (by
    decide)
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct unitInput tail
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide : (0 : Fraction.Rational) ≤ 1)
  simpa only [Fraction.Field.one_mul] using product
end Purelib.Approximation.Gaussian.Exponential.Taylor.Bounds

end
