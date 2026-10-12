module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Horner.Taylor
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
import Purelib.Polynomial.Ascending.Gaussian.Derivative
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Polynomial.Ascending.Gaussian.Integral
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic
import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Derivative
import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Evaluation
import Init.Prelude
import Purelib.Polynomial.Ascending.Gaussian.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Taylor

open Purelib.Polynomial

open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding

section
@[expose] public section

/-!
# Exact integration and finite reading bounds for exponential polynomials

`polynomial n` has degree `n+1`, matching the existing finite Horner sample
at index `n`.  Its integral has the next sample index.  All statements concern
displayed coefficient lists and rational points, not a completed exponential.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Integral

/-- Embed the finite rational exponential polynomial of degree index plus one into Gaussian coefficients. -/
def polynomial (index : Nat) :
  Polynomial.Ascending.Gaussian.CoefficientPolynomial :=
  RationalEmbedding.Basic.ofRational (Polynomial.exponential (index + 1))

/-- Evaluating the Gaussian exponential polynomial equals the finite Horner sample at the retained index. -/
theorem eval_polynomial (index : Nat) (input :
  Data.Gaussian.Basic.Canonical) :
    Evaluation.eval (polynomial index) input = Sample.sample input
      index := by
  rw [polynomial, Evaluation.eval_ofRational,
    Polynomial.eval_exponential,
    Taylor.sample_eq_truncatedExp]

/-- The coefficientwise derivative of the next Gaussian exponential polynomial is the preceding one. -/
theorem derivative_next (index : Nat) :
    Coefficient.CoefficientwiseEqual (Derivative.derivative
      (polynomial (index + 1)))
      (polynomial index) := by
  unfold polynomial
  rw [Derivative.derivative_ofRational]
  exact Evaluation.ofRational_coefficientwise (Polynomial.derivative_exponential_succ (index + 1))

/-- The `+1` on the right is essential: the source polynomial already has degree `index+1`, and integration raises that
degree once more. -/
theorem integral_polynomial (index : Nat) :
    Integral.definiteIntegral (polynomial index) 0 1 = Sample.sample
      1 (index + 1) - 1 := by
  rw [← Integral.definiteIntegral_eq_of_coefficientwise
    (derivative_next index) 0 1,
    Integral.definiteIntegral_derivative, eval_polynomial,
      eval_polynomial, Sample.sample_zero]
end Purelib.Approximation.Gaussian.Exponential.Taylor.Integral

end
