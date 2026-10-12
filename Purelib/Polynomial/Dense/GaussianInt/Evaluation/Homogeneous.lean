module
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation
import Purelib.Algebra.Semiring.Normalization
import Purelib.Tactic.Ring

open Purelib.Data
open Purelib.Polynomial

section
@[expose] public section

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous

open Purelib.Data
open Purelib.Algebra.Semiring
open Purelib.Polynomial.Dense.GaussianInt

/-- High-to-low homogeneous evaluation with a Gaussian-integer denominator. -/
def homogeneousEval (numerator denominator :
  GaussianInt) :
    List GaussianInt → GaussianInt
  | [] => 0
  | coefficient :: remaining =>
      coefficient * numerator ^ remaining.length +
        denominator * homogeneousEval numerator denominator
          remaining

/-- Gaussian homogeneous evaluation is ordinary evaluation multiplied by the
exact Gaussian denominator power.

The retained numerator and nonzero Gaussian denominator determine the affine
input. The homogeneous coefficient recursion equals affine evaluation times the
corresponding denominator power. -/
theorem homogeneousEval_cons_eq_scaled
    (fraction : GaussianInt.Fraction) (coefficient : GaussianInt)
    (remaining : List GaussianInt) :
    GaussianInt.toGaussian
        (homogeneousEval fraction.numerator fraction.denominator
          (coefficient :: remaining)) =
      GaussianInt.toGaussian fraction.denominator ^ remaining.length *
        Dense.GaussianInt.Evaluation.evalIntegers fraction.value
          (coefficient :: remaining) := by
  induction remaining generalizing coefficient with
  | nil =>
      have homogeneousSingleton :
          homogeneousEval fraction.numerator fraction.denominator
            [coefficient] = coefficient := by
        change coefficient * fraction.numerator ^ 0 + fraction.denominator * 0 = coefficient
        rw [pow_zero, mul_one, mul_zero, add_zero]
      have evaluatedSingleton : Evaluation.evalIntegers fraction.value [coefficient] =
          GaussianInt.toGaussian coefficient := by
        rw [Evaluation.evalIntegers_cons, Evaluation.evalIntegers_nil, List.length_nil,
          pow_zero, mul_one, add_zero]
      rw [homogeneousSingleton, evaluatedSingleton, List.length_nil, pow_zero, one_mul]
  | cons next remaining inductionHypothesis =>
      have cleared := fraction.value_mul_denominator
      rw [homogeneousEval, GaussianInt.toGaussian_add,
        GaussianInt.toGaussian_mul]
      rw [Data.GaussianInt.toGaussian_pow,
        GaussianInt.toGaussian_mul, inductionHypothesis]
      rw [Dense.GaussianInt.Evaluation.evalIntegers_cons fraction.value coefficient
        (next :: remaining), List.length_cons, pow_succ]
      rw [← cleared]
      rw [Normalization.product_pow, pow_succ]
      ring1
end Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous

end
