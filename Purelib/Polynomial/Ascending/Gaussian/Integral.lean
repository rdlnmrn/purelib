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
  Evaluation.eval (Antiderivative.antiderivative polynomial) finish -
    Evaluation.eval (Antiderivative.antiderivative polynomial) start

/-- The exact Gaussian polynomial integral of zero vanishes.

The zero coefficient table has a zero antiderivative at both supplied endpoints,
so their difference is zero independently of the endpoint values. -/
@[simp] theorem definiteIntegral_zero (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral Basic.zero start finish = 0 := by
  change ((0 : Gaussian.Basic.Canonical) + finish * 0) - (0 + start * 0) = 0
  rw [Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero, _root_.add_zero]
  exact _root_.sub_self (0 : Gaussian.Basic.Canonical)

/-- The exact integral of a constant is its value times the endpoint displacement. -/
@[simp] theorem definiteIntegral_constant (value start finish : Gaussian.Basic.Canonical) :
    definiteIntegral (Basic.constant value) start finish =
      value * (finish - start) := by
  unfold definiteIntegral Antiderivative.antiderivative Basic.constant
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
    (equal : Coefficient.CoefficientwiseEqual left right) (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral left start finish = definiteIntegral right start finish := by
  unfold definiteIntegral
  rw [Evaluation.eval_eq_of_coefficientwise
    (Antiderivative.coefficientwise_antiderivative equal) finish,
    Evaluation.eval_eq_of_coefficientwise
      (Antiderivative.coefficientwise_antiderivative equal) start]

/-- The finite algebraic FTC, without a supplied primitive certificate. -/
theorem definiteIntegral_derivative (polynomial : CoefficientPolynomial) (start finish :
  Gaussian.Basic.Canonical) :
    definiteIntegral (Derivative.derivative polynomial) start finish =
      Evaluation.eval polynomial finish - Evaluation.eval polynomial start := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil =>
          change definiteIntegral Basic.zero start finish = Evaluation.eval
            Basic.zero finish - Evaluation.eval Basic.zero
            start
          rw [definiteIntegral_zero, Evaluation.eval_zero, Evaluation.eval_zero,
            _root_.sub_self]
      | cons head tail =>
          change Evaluation.evalCoeffs (0 ::
            Antiderivative.antiderivativeCoefficients 0 (Derivative.derivativeFrom
            1 tail)) finish -
              Evaluation.evalCoeffs (0 ::
                Antiderivative.antiderivativeCoefficients 0
                (Derivative.derivativeFrom 1 tail)) start =
            Evaluation.evalCoeffs (head :: tail) finish - Evaluation.evalCoeffs
              (head :: tail) start
          rw [show 1 = 0 + 1 from rfl, Antiderivative.antiderivativeCoefficients_derivativeFrom]
          simp only [Evaluation.evalCoeffs_cons]
          ring1

/-- The exact Gaussian polynomial integral preserves addition. -/
theorem definiteIntegral_add (left right : CoefficientPolynomial) (start finish :
  Gaussian.Basic.Canonical) :
    definiteIntegral (Arithmetic.add left right) start finish =
      definiteIntegral left start finish + definiteIntegral right start finish := by
  unfold definiteIntegral
  rw [Evaluation.eval_eq_of_coefficientwise (Antiderivative.antiderivative_add
    left right) finish,
    Evaluation.eval_eq_of_coefficientwise (Antiderivative.antiderivative_add left
      right) start, Evaluation.eval_add, Evaluation.eval_add]
  ring1

/-- The exact Gaussian polynomial integral commutes with Gaussian scaling. -/
theorem definiteIntegral_scale (factor : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral (Arithmetic.scale factor polynomial) start finish =
      factor * definiteIntegral polynomial start finish := by
  unfold definiteIntegral
  rw [Evaluation.eval_eq_of_coefficientwise (Antiderivative.antiderivative_scale
    factor polynomial) finish,
    Evaluation.eval_eq_of_coefficientwise (Antiderivative.antiderivative_scale
      factor polynomial) start,
    Evaluation.eval_scale, Evaluation.eval_scale]
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
