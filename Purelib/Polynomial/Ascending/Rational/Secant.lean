module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Derivative
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.Polynomial.Ascending.Rational.Secant

/-! ## Dense finite polynomials -/

/-- Secant kernel for a low-to-high finite coefficient list.  The constant
coefficient disappears structurally, while the tail is evaluated by the
same finite Horner program as the original polynomial. -/
def coefficientsKernel (x y : Gaussian.Basic.Canonical) : List
  Fraction.Rational → Gaussian.Basic.Canonical
  | [] => 0
  | _constant :: remaining =>
      Ascending.Rational.GaussianEvaluation.evalCoefficients x remaining + y *
        coefficientsKernel x y remaining

/-- Compute the finite secant kernel of the retained coefficient table at two Gaussian arguments. -/
def polynomialKernel (polynomial :
  CoefficientPolynomial) (x y : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  coefficientsKernel x y polynomial.coefficients

/-- The difference of two Horner values factors through the argument difference and the finite secant kernel.

The identity holds even when the arguments coincide; no division by their difference is used. -/
theorem evalCoefficients_sub_factor (x y : Gaussian.Basic.Canonical)
  : ∀ coefficients,
    Ascending.Rational.GaussianEvaluation.evalCoefficients x coefficients -
      Ascending.Rational.GaussianEvaluation.evalCoefficients y coefficients =
      (x - y) * coefficientsKernel x y coefficients
  | [] => by
      change (0 : Gaussian.Basic.Canonical) - 0 = (x - y) * 0
      exact (Gaussian.Basic.sub_self 0).trans (Gaussian.Basic.mul_zero _).symm
  | coefficient :: remaining => by
      rw [Ascending.Rational.GaussianEvaluation.evalCoefficients_cons,
        Ascending.Rational.GaussianEvaluation.evalCoefficients_cons, coefficientsKernel]
      calc
        (Purelib.Data.Gaussian.Scale.scale coefficient 1 +
              x * Ascending.Rational.GaussianEvaluation.evalCoefficients x remaining) -
            (Purelib.Data.Gaussian.Scale.scale coefficient 1 +
              y * Ascending.Rational.GaussianEvaluation.evalCoefficients y remaining) =
            (x - y) * Ascending.Rational.GaussianEvaluation.evalCoefficients x remaining +
              y * (Ascending.Rational.GaussianEvaluation.evalCoefficients x remaining -
                Ascending.Rational.GaussianEvaluation.evalCoefficients y remaining) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1
        _ = (x - y) * Ascending.Rational.GaussianEvaluation.evalCoefficients x remaining +
            y * ((x - y) * coefficientsKernel x y remaining) := by
          rw [evalCoefficients_sub_factor x y remaining]
        _ = (x - y) *
            (Ascending.Rational.GaussianEvaluation.evalCoefficients x remaining +
              y * coefficientsKernel x y remaining) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1

/-- Every finite polynomial difference is factored by the displayed input
difference using the constructed kernel. -/
theorem eval_sub_factor (polynomial :
  CoefficientPolynomial) (x y : Gaussian.Basic.Canonical) :
    Ascending.Rational.GaussianEvaluation.eval polynomial x - Ascending.Rational.GaussianEvaluation.eval polynomial y =
      (x - y) * polynomialKernel polynomial x y :=
  evalCoefficients_sub_factor x y polynomial.coefficients

/-- Evaluate a degree-weighted coefficient table using its original value and diagonal secant kernel.

The starting weight scales the original value, and the argument times the diagonal kernel supplies the additional degree
weights. -/
private theorem derivativeFrom_eval_identity (x :
  Gaussian.Basic.Canonical) :
    ∀ (factor : Nat) (coefficients : List Fraction.Rational),
      Ascending.Rational.GaussianEvaluation.evalCoefficients x (Ascending.Rational.Derivative.derivativeFrom factor
        coefficients) =
        Purelib.Data.Gaussian.Scale.scale (factor : Fraction.Rational)
            (Ascending.Rational.GaussianEvaluation.evalCoefficients x coefficients) +
          x * coefficientsKernel x x coefficients
  | factor, [] => by
      simp only [Ascending.Rational.Derivative.derivativeFrom,
        Ascending.Rational.GaussianEvaluation.evalCoefficients_nil, coefficientsKernel,
        Gaussian.Basic.mul_zero, _root_.add_zero]
      apply Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Scale.scale_re,
          Purelib.Data.Gaussian.Scale.scale_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | factor, coefficient :: remaining => by
      rw [Ascending.Rational.Derivative.derivativeFrom, Ascending.Rational.GaussianEvaluation.evalCoefficients_cons,
        Ascending.Rational.GaussianEvaluation.evalCoefficients_cons,
        coefficientsKernel,
        derivativeFrom_eval_identity x (factor + 1) remaining]
      rw [Fraction.Cast.natCast_add_direct, Nat.cast_one]
      apply Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Scale.scale_re,
          Purelib.Data.Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- The diagonal of the polynomial secant kernel is exactly the evaluation
of the already executable formal derivative. -/
theorem polynomialKernel_diagonal (polynomial :
  CoefficientPolynomial) (x : Gaussian.Basic.Canonical) :
    polynomialKernel polynomial x x = Ascending.Rational.GaussianEvaluation.eval
      (Ascending.Rational.Derivative.derivative polynomial) x := by
  cases polynomial with
  | mk coefficients =>
    cases coefficients with
    | nil => rfl
    | cons constant remaining =>
      change coefficientsKernel x x (constant :: remaining) =
        Ascending.Rational.GaussianEvaluation.evalCoefficients x (Ascending.Rational.Derivative.derivativeFrom 1
          remaining)
      rw [coefficientsKernel,
        derivativeFrom_eval_identity x 1 remaining]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im, Nat.cast_one] <;> ring1

end Purelib.Polynomial.Ascending.Rational.Secant

end
