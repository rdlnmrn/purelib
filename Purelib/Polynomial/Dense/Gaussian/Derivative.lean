module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.GaussianCanonical (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Derivative

/-- Finite automatic differentiation of a dense coefficient list. -/
def derivative (polynomial :
  CoefficientPolynomial) : (Dense.Basic.DensePolynomial
    Gaussian.Basic.Canonical) :=
  Dense.Derivative.derivative polynomial

/-- Removing leading zero coefficients preserves the Gaussian derivative polynomial. -/
theorem derivative_normalize (polynomial :
  CoefficientPolynomial) :
    derivative (Dense.Gaussian.Basic.normalize polynomial) =
      derivative polynomial :=
  Dense.Derivative.derivative_normalize polynomial

/-- Evaluation of both polynomial jet components commutes with the finite derivative fold.

The identity permits an arbitrary initial polynomial value-and-derivative state. -/
private theorem eval_derivative_fold
    (point : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical)
    (state : CoefficientPolynomial ×
      CoefficientPolynomial) :
    ((coefficients.foldl
        Dense.Derivative.derivativeStep state).1.eval point,
      (coefficients.foldl
        Dense.Derivative.derivativeStep state).2.eval point) =
      coefficients.foldl
        (Dense.Derivative.evalDerivativeStep point)
        (state.1.eval point, state.2.eval point) := by
  induction coefficients generalizing state with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      apply congrArg (fun nextState : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical =>
        coefficients.foldl
          (Dense.Derivative.evalDerivativeStep point) nextState)
      apply Prod.ext
      · simp only [Dense.Derivative.derivativeStep,
          Dense.Derivative.evalDerivativeStep]
        rw [DensePolynomial.eval_add,
          Dense.Gaussian.Arithmetic.eval_shift_one,
          DensePolynomial.eval_constant]
      · simp only [Dense.Derivative.derivativeStep,
          Dense.Derivative.evalDerivativeStep]
        rw [DensePolynomial.eval_add,
          Dense.Gaussian.Arithmetic.eval_shift_one]

/-- The derivative evaluator is the second component of the same finite
automatic-differentiation Horner scan. -/
theorem eval_derivative (polynomial :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Evaluation.eval (derivative polynomial) point =
      (Dense.Derivative.evalDerivativeCoeffs
        point polynomial.coeffs).2 := by
  unfold Dense.Gaussian.Evaluation.eval derivative Dense.Derivative.derivative
    Dense.Derivative.derivativeState
    Dense.Derivative.evalDerivativeCoeffs
  have specification := eval_derivative_fold point polynomial.coeffs
    ((0 : CoefficientPolynomial), (0 :
      CoefficientPolynomial))
  exact congrArg Prod.snd specification

end Purelib.Polynomial.Dense.Gaussian.Derivative

end
