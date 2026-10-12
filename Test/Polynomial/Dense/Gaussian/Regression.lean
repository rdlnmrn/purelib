module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative
import Purelib.Polynomial.Dense.Gaussian.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Multiplication
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Basic

@[expose] public section

/-!
# Executable regression table for canonical dense polynomials

The closed checks exercise every operation in the dense-polynomial pilot in
both the kernel and the compiled evaluator.
-/

namespace Test.Polynomial.Dense.Gaussian.Regression

open scoped Purelib.Data.Nat

/-- The canonical dense Gaussian polynomial X plus one. -/
private def variablePlusOne : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 1]⟩
/-- The canonical dense Gaussian polynomial X minus one. -/
private def variableMinusOne : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, -1]⟩
/-- The displayed polynomial X plus one with two retained leading zero coefficients. -/
private def displayedWithLeadingZeros : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[0, 0, 1, 1]⟩
/-- The canonical dense Gaussian polynomial twice X. -/
private def twiceVariable : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[2, 0]⟩
/-- The canonical dense Gaussian polynomial X squared minus one. -/
private def squareMinusOne : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -1]⟩
/-- The constant unit Gaussian polynomial. -/
private def onePolynomial : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1]⟩
/-- The exact value negative one plus twice the imaginary unit. -/
private def valueAtGamma : Data.Gaussian.Basic.Canonical := ⟨-1, 2⟩

/-- Dense normalization removes the two displayed leading zeros. -/
theorem regression_normalize :
    Dense.Gaussian.Basic.normalize (⟨[0, 0, 1, 1]⟩ :
      Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) = (⟨[1, 1]⟩ :
      Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) :=
      by
  decide

/-- Dense addition of X plus one and X minus one produces twice X. -/
theorem regression_add :
    Dense.Gaussian.Arithmetic.add (⟨[1, 1]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial)
      (⟨[1, -1]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) =
      (⟨[2, 0]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) := by
  decide

/-- Dense multiplication of X plus one and X minus one produces X squared minus one. -/
theorem regression_mul :
    Multiplication.mul (⟨[1, 1]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) (⟨[1, -1]⟩
      : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) =
      (⟨[1, 0, -1]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) := by
  decide

/-- The dense derivative of X plus one is the constant unit polynomial. -/
theorem regression_derivative :
    Derivative.derivative (⟨[1, 1]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) = (⟨[1]⟩
      : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial) := by
  decide

/-- Exact Horner evaluation of X squared minus one at one plus the imaginary unit is negative one plus twice the
imaginary unit. -/
theorem regression_horner :
    Evaluation.eval (⟨[1, 0, -1]⟩ : Polynomial.Dense.Gaussian.Basic.GaussianCanonical.CoefficientPolynomial)
      Data.Gaussian.Basic.Canonical.gamma =
      (⟨-1, 2⟩ : Data.Gaussian.Basic.Canonical) := by
  decide

open Test.Polynomial.Dense.Gaussian.Regression in
/-- One executable Boolean used by the compiled regression runner. -/
def compiledPolynomialRegressionPassed : Bool :=
  let displayedWithLeadingZeros : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[0, 0, 1, 1]⟩
  let variablePlusOne : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 1]⟩
  let variableMinusOne : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, -1]⟩
  let twiceVariable : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[2, 0]⟩
  let squareMinusOne : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -1]⟩
  let onePolynomial : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1]⟩
  let valueAtGamma : Data.Gaussian.Basic.Canonical := ⟨-1, 2⟩
  decide (Dense.Gaussian.Basic.normalize displayedWithLeadingZeros = variablePlusOne) &&
    decide (Dense.Gaussian.Arithmetic.add variablePlusOne variableMinusOne = twiceVariable) &&
    decide (Multiplication.mul variablePlusOne variableMinusOne = squareMinusOne) &&
    decide (Derivative.derivative variablePlusOne = onePolynomial) &&
    decide (Evaluation.eval squareMinusOne Data.Gaussian.Basic.Canonical.gamma =
      valueAtGamma)

/-- The executable dense Gaussian polynomial regression table passes. -/
theorem compiledPolynomialRegressionPassed_eq_true :
    Regression.compiledPolynomialRegressionPassed = true := by
  decide

end Test.Polynomial.Dense.Gaussian.Regression
