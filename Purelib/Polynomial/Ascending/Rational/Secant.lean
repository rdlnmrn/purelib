module
public import Purelib.Polynomial.Ascending.Gaussian.Secant
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

public section

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
@[expose] def coefficientsKernel (x y : Gaussian.Basic.Canonical) : List Fraction.Rational → Gaussian.Basic.Canonical :=
  Ascending.Gaussian.Secant.coefficientsKernel GaussianEvaluation.evalCoefficients x y

/-- The shared original secant traversal returns zero for an empty original rational coefficient table. -/
theorem coefficientsKernel_nil (x y : Gaussian.Basic.Canonical) : coefficientsKernel x y [] = 0 := rfl

/-- The shared original secant traversal reads the same original rational coefficient tail at its successor branch. -/
theorem coefficientsKernel_cons (x y : Gaussian.Basic.Canonical) (head : Fraction.Rational)
    (tail : List Fraction.Rational) :
    coefficientsKernel x y (head :: tail) =
      GaussianEvaluation.evalCoefficients x tail + y * coefficientsKernel x y tail := rfl

end Purelib.Polynomial.Ascending.Rational.Secant

end

@[expose] public section

namespace Purelib.Polynomial.Ascending.Rational.Secant

/-- Compute the finite secant kernel of the retained coefficient table at two Gaussian arguments. -/
def polynomialKernel (polynomial :
  CoefficientPolynomial) (x y : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  coefficientsKernel x y polynomial.coefficients

/-- The difference of two Horner values factors through the argument difference and the finite secant kernel.

The identity holds even when the arguments coincide; no division by their difference is used. -/
theorem evalCoefficients_sub_factor (x y : Gaussian.Basic.Canonical) : ∀ coefficients,
    GaussianEvaluation.evalCoefficients x coefficients - GaussianEvaluation.evalCoefficients y coefficients =
      (x - y) * coefficientsKernel x y coefficients :=
  Ascending.Gaussian.Secant.evalCoefficients_sub_factor GaussianEvaluation.evalCoefficients
    (fun coefficient => Gaussian.Scale.scale coefficient 1) (fun _ => rfl) (fun _ _ _ => rfl) x y

/-- Every finite polynomial difference is factored by the displayed input
difference using the constructed kernel. -/
theorem eval_sub_factor (polynomial :
  CoefficientPolynomial) (x y : Gaussian.Basic.Canonical) :
    GaussianEvaluation.eval polynomial x - GaussianEvaluation.eval polynomial y =
      (x - y) * polynomialKernel polynomial x y :=
  evalCoefficients_sub_factor x y polynomial.coefficients

/-- Evaluate a degree-weighted coefficient table using its original value and diagonal secant kernel.

The starting weight scales the original value, and the argument times the diagonal kernel supplies the additional degree
weights. -/
private theorem derivativeFrom_eval_identity (x :
  Gaussian.Basic.Canonical) :
    ∀ (factor : Nat) (coefficients : List Fraction.Rational),
      GaussianEvaluation.evalCoefficients x (Derivative.derivativeFrom factor
        coefficients) =
        Gaussian.Scale.scale (factor : Fraction.Rational)
            (GaussianEvaluation.evalCoefficients x coefficients) +
          x * coefficientsKernel x x coefficients
  | factor, [] => by
      simp only [Derivative.derivativeFrom,
        GaussianEvaluation.evalCoefficients_nil, coefficientsKernel_nil,
        Gaussian.Basic.mul_zero, _root_.add_zero]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | factor, coefficient :: remaining => by
      rw [Derivative.derivativeFrom, GaussianEvaluation.evalCoefficients_cons,
        GaussianEvaluation.evalCoefficients_cons,
        coefficientsKernel_cons,
        derivativeFrom_eval_identity x (factor + 1) remaining]
      rw [Fraction.Cast.natCast_add_direct, Nat.cast_one]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- The diagonal of the polynomial secant kernel is exactly the evaluation
of the already executable formal derivative. -/
theorem polynomialKernel_diagonal (polynomial :
  CoefficientPolynomial) (x : Gaussian.Basic.Canonical) :
    polynomialKernel polynomial x x = GaussianEvaluation.eval
      (Derivative.derivative polynomial) x := by
  cases polynomial with
  | mk coefficients =>
    cases coefficients with
    | nil => rfl
    | cons constant remaining =>
      change coefficientsKernel x x (constant :: remaining) =
        GaussianEvaluation.evalCoefficients x (Derivative.derivativeFrom 1
          remaining)
      rw [coefficientsKernel_cons,
        derivativeFrom_eval_identity x 1 remaining]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im, Nat.cast_one] <;> ring1

end Purelib.Polynomial.Ascending.Rational.Secant

end
