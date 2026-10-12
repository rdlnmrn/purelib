module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator

/-- High-to-low homogeneous Gaussian-integer evaluation. -/
def homogeneousEval (numerator :
  GaussianInt) (denominator : Nat) :
    List GaussianInt → GaussianInt
  | [] => 0
  | coefficient :: remaining =>
      coefficient * numerator ^ remaining.length +
        GaussianInt.ofNat denominator *
          homogeneousEval numerator
            denominator remaining

/-- Homogeneous evaluation is ordinary evaluation multiplied by the exact
denominator power. -/
theorem
  homogeneousEval_cons_eq_scaled
    (fraction : Gaussian.Basic.Canonical.Fraction.NaturalDenominator) (coefficient : GaussianInt)
    (remaining : List GaussianInt) :
    GaussianInt.toGaussian
        (homogeneousEval fraction.numerator
          fraction.denominator
          (coefficient :: remaining)) =
      ⟨(fraction.denominator : Fraction.Rational), 0⟩ ^ remaining.length *
        Dense.GaussianInt.Evaluation.evalIntegers fraction.value (coefficient :: remaining) := by
  induction remaining generalizing coefficient with
  | nil =>
      simp [-eq_self, -iff_self, homogeneousEval,
        Dense.GaussianInt.Evaluation.evalIntegers]
      rfl
  | cons next remaining inductionHypothesis =>
      have cleared := fraction.value_mul_denominator
      rewrite [GaussianInt.toGaussian_ofNat] at cleared
      change fraction.value * ⟨(fraction.denominator : Fraction.Rational), 0⟩ =
        GaussianInt.toGaussian
          fraction.numerator at cleared
      rw [homogeneousEval,
        GaussianInt.toGaussian_add,
        GaussianInt.toGaussian_mul]
      rw [Data.GaussianInt.toGaussian_pow,
        GaussianInt.toGaussian_mul,
        GaussianInt.toGaussian_ofNat,
        inductionHypothesis]
      rw [Dense.GaussianInt.Evaluation.evalIntegers_cons fraction.value coefficient (next :: remaining),
        List.length_cons, pow_succ]
      rw [← cleared]
      have productPower :
          (fraction.value * (⟨(fraction.denominator : Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical)) ^
              remaining.length =
            fraction.value ^ remaining.length *
              (⟨(fraction.denominator : Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical) ^ remaining.length := by
        induction remaining.length with
        | zero =>
            simp only [-eq_self, -iff_self, pow_zero, Gaussian.Basic.one_mul]
            rfl
        | succ exponent inductionPower =>
            rw [pow_succ, pow_succ, pow_succ, inductionPower]
            ring1
      rw [productPower, pow_succ]
      ring1
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator

end
