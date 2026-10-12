module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
import Purelib.Polynomial.Ascending.Gaussian.Derivative
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Tactic.Ring

/-!
# Exact Gaussian polynomial integration

Endpoint evaluation of the finite zero-constant antiderivative defines the
integral. Coefficientwise equality, differentiation, linearity and interval
concatenation are proved from the retained finite coefficient tables.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Integral

open Purelib.Data
open Purelib.Polynomial

public section

/-- Evaluate the zero-constant antiderivative at two supplied endpoints.

The integral is the final value minus the initial value of the exact finite
Gaussian antiderivative. No endpoint ordering or analytic primitive is required. -/
@[expose] def definiteIntegral (polynomial : CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Antiderivative.antiderivative polynomial) finish -
    Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Antiderivative.antiderivative polynomial) start

/-- The exact Gaussian polynomial integral of zero vanishes.

The zero coefficient table has a zero antiderivative at both supplied endpoints,
so their difference is zero independently of the endpoint values. -/
@[simp] theorem definiteIntegral_zero (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral Ascending.Gaussian.Basic.zero start finish = 0 := by
  change ((0 : Gaussian.Basic.Canonical) + finish * 0) - (0 + start * 0) = 0
  rw [Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero, _root_.add_zero]
  exact _root_.sub_self (0 : Gaussian.Basic.Canonical)

/-- The exact integral of a constant is its value times the endpoint displacement. -/
@[simp] theorem definiteIntegral_constant (value start finish : Gaussian.Basic.Canonical) :
    definiteIntegral (Ascending.Gaussian.Basic.constant value) start finish =
      value * (finish - start) := by
  unfold definiteIntegral Ascending.Gaussian.Antiderivative.antiderivative Ascending.Gaussian.Basic.constant
  change (0 + finish * (value / (1 : Gaussian.Basic.Canonical) + finish * 0)) -
      (0 + start * (value / (1 : Gaussian.Basic.Canonical) + start * 0)) =
    value * (finish - start)
  have divOne : value / (1 : Gaussian.Basic.Canonical) = value := by
    change value * (1 : Gaussian.Basic.Canonical)⁻¹ = value
    rw [Gaussian.Field.inv_eq,
      Gaussian.Field.inv_one_direct,
      _root_.mul_one]
  rw [divOne]
  apply Gaussian.Basic.ext <;>
    simp only [_root_.zero_add,
      Gaussian.Basic.mul_zero,
      _root_.add_zero,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
    ring1

/-- Reversing the two endpoints negates the exact Gaussian polynomial integral. -/
theorem definiteIntegral_reverse (polynomial : CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral polynomial finish start =
      -definiteIntegral polynomial start finish := by
  unfold definiteIntegral
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1

/-- Coefficientwise equal Gaussian polynomials have the same exact integral between the supplied endpoints. -/
theorem definiteIntegral_eq_of_coefficientwise {left right : CoefficientPolynomial}
    (equal : Ascending.Gaussian.Coefficient.CoefficientwiseEqual left right) (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral left start finish = definiteIntegral right start finish := by
  unfold definiteIntegral
  rw [Ascending.Gaussian.Evaluation.eval_eq_of_coefficientwise
    (Ascending.Gaussian.Antiderivative.coefficientwise_antiderivative equal) finish,
    Ascending.Gaussian.Evaluation.eval_eq_of_coefficientwise
      (Ascending.Gaussian.Antiderivative.coefficientwise_antiderivative equal) start]

/-- The finite algebraic FTC, without a supplied primitive certificate. -/
theorem definiteIntegral_derivative (polynomial : CoefficientPolynomial) (start finish :
  Gaussian.Basic.Canonical) :
    definiteIntegral (Ascending.Gaussian.Derivative.derivative polynomial) start finish =
      Ascending.Gaussian.Evaluation.eval polynomial finish - Ascending.Gaussian.Evaluation.eval polynomial start := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil =>
          change definiteIntegral Ascending.Gaussian.Basic.zero start finish = Ascending.Gaussian.Evaluation.eval
            Ascending.Gaussian.Basic.zero finish - Ascending.Gaussian.Evaluation.eval Ascending.Gaussian.Basic.zero
            start
          rw [definiteIntegral_zero, Ascending.Gaussian.Evaluation.eval_zero, Ascending.Gaussian.Evaluation.eval_zero,
            _root_.sub_self]
      | cons head tail =>
          change Ascending.Gaussian.Evaluation.evalCoeffs (0 ::
            Ascending.Gaussian.Antiderivative.antiderivativeCoefficients 0 (Ascending.Gaussian.Derivative.derivativeFrom
            1 tail)) finish -
              Ascending.Gaussian.Evaluation.evalCoeffs (0 ::
                Ascending.Gaussian.Antiderivative.antiderivativeCoefficients 0
                (Ascending.Gaussian.Derivative.derivativeFrom 1 tail)) start =
            Ascending.Gaussian.Evaluation.evalCoeffs (head :: tail) finish - Ascending.Gaussian.Evaluation.evalCoeffs
              (head :: tail) start
          rw [show 1 = 0 + 1 from rfl, Ascending.Gaussian.Antiderivative.antiderivativeCoefficients_derivativeFrom]
          simp only [Ascending.Gaussian.Evaluation.evalCoeffs_cons]
          ring1

/-- The exact Gaussian polynomial integral preserves addition. -/
theorem definiteIntegral_add (left right : CoefficientPolynomial) (start finish :
  Gaussian.Basic.Canonical) :
    definiteIntegral (Ascending.Gaussian.Arithmetic.add left right) start finish =
      definiteIntegral left start finish + definiteIntegral right start finish := by
  unfold definiteIntegral
  rw [Ascending.Gaussian.Evaluation.eval_eq_of_coefficientwise (Ascending.Gaussian.Antiderivative.antiderivative_add
    left right) finish,
    Ascending.Gaussian.Evaluation.eval_eq_of_coefficientwise (Ascending.Gaussian.Antiderivative.antiderivative_add left
      right) start, Ascending.Gaussian.Evaluation.eval_add, Ascending.Gaussian.Evaluation.eval_add]
  ring1

/-- The exact Gaussian polynomial integral commutes with Gaussian scaling. -/
theorem definiteIntegral_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral (Ascending.Gaussian.Arithmetic.scale factor polynomial) start finish =
      factor * definiteIntegral polynomial start finish := by
  unfold definiteIntegral
  rw [Ascending.Gaussian.Evaluation.eval_eq_of_coefficientwise (Ascending.Gaussian.Antiderivative.antiderivative_scale
    factor polynomial) finish,
    Ascending.Gaussian.Evaluation.eval_eq_of_coefficientwise (Ascending.Gaussian.Antiderivative.antiderivative_scale
      factor polynomial) start,
    Ascending.Gaussian.Evaluation.eval_scale, Ascending.Gaussian.Evaluation.eval_scale]
  ring1

/-- Adjacent displayed intervals telescope without any endpoint ordering assumption. -/
theorem definiteIntegral_concat (polynomial : CoefficientPolynomial) (start middle finish :
  Gaussian.Basic.Canonical) :
    definiteIntegral polynomial start finish =
      definiteIntegral polynomial start middle + definiteIntegral polynomial middle finish := by
  unfold definiteIntegral
  ring1

end

end Purelib.Polynomial.Ascending.Gaussian.Integral
