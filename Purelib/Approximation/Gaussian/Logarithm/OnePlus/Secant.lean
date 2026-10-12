module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial.Evaluation
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample
import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Secant

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.OnePlus

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial

open Purelib.Polynomial.Ascending.Rational

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Secant

/-- The actual two-input secant kernel for the same finite local-log polynomial used by `log1pSample`. -/
def log1pSecantKernel (x y :
  Canonical) (index : Nat) : Canonical :=
  Secant.polynomialKernel
    (Polynomial.log1pPolynomial index) x y

/-- The difference of two equal-depth finite logarithm samples factors as the input difference times their polynomial
secant kernel. -/
theorem log1pSample_sub_factor (x y :
  Canonical) (index : Nat) :
    Sample.log1pSample x index - Sample.log1pSample y index =
      (x - y) * log1pSecantKernel x y index := by
  calc
    Sample.log1pSample x index - Sample.log1pSample y index =
        GaussianEvaluation.eval (Polynomial.log1pPolynomial index) x -
          GaussianEvaluation.eval (Polynomial.log1pPolynomial index) y := by
      rw [Evaluation.eval_log1pPolynomial, Evaluation.eval_log1pPolynomial]
    _ = (x - y) *
        Secant.polynomialKernel
          (Polynomial.log1pPolynomial index) x y :=
      Secant.eval_sub_factor
        (Polynomial.log1pPolynomial index) x y

/-- Diagonal substitution in the constructed local-log secant kernel is exactly the finite geometric derivative program.
-/
theorem log1pSecantKernel_diagonal (u :
  Canonical) (index : Nat) :
    log1pSecantKernel u u index = Sample.log1pDerivativeSample u index
      := by
  calc
    log1pSecantKernel u u index =
        GaussianEvaluation.eval (Derivative.derivative (Polynomial.log1pPolynomial index)) u :=
      Secant.polynomialKernel_diagonal
        (Polynomial.log1pPolynomial index) u
    _ = GaussianEvaluation.eval (Polynomial.log1pGeometricPolynomial index) u :=
      GaussianEvaluation.eval_eq_of_coefficientwise (Polynomial.derivative_log1pPolynomial index) u
    _ = Sample.log1pDerivativeSample u index :=
      Evaluation.eval_log1pGeometricPolynomial u index
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Secant

end
