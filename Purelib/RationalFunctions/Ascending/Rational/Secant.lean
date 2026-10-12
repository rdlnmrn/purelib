module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Division
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.Secant
import Purelib.RationalFunctions.Ascending.Rational.Basic
public import Purelib.RationalFunctions.Ascending.Rational.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field

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

namespace Purelib.RationalFunctions.Ascending.Rational.Basic
namespace RationalPolynomial

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The rational secant kernel factors the difference of two evaluations.

The denominator evaluations at both Gaussian points are explicitly nonzero. Their quotient-rule kernel multiplies the
argument difference to recover the exact value difference. -/
theorem eval_sub_factor (expression :
  Ascending.Rational.Basic.RationalPolynomial) (x y : Gaussian.Basic.Canonical)
    (xDenominatorNonzero :
      Ascending.Rational.GaussianEvaluation.eval expression.denominator x ≠ 0)
    (yDenominatorNonzero :
      Ascending.Rational.GaussianEvaluation.eval expression.denominator y ≠ 0) :
    expression.eval x - expression.eval y =
      (x - y) * expression.kernel x y := by
  let numeratorX :=
    Ascending.Rational.GaussianEvaluation.eval expression.numerator x
  let numeratorY :=
    Ascending.Rational.GaussianEvaluation.eval expression.numerator y
  let denominatorX :=
    Ascending.Rational.GaussianEvaluation.eval expression.denominator x
  let denominatorY :=
    Ascending.Rational.GaussianEvaluation.eval expression.denominator y
  let numeratorKernel := Ascending.Rational.Secant.polynomialKernel expression.numerator x y
  let denominatorKernel := Ascending.Rational.Secant.polynomialKernel expression.denominator x y
  have numeratorFactor : numeratorX - numeratorY =
      (x - y) * numeratorKernel :=
    Ascending.Rational.Secant.eval_sub_factor
      expression.numerator x y
  have denominatorFactor : denominatorX - denominatorY =
      (x - y) * denominatorKernel :=
    Ascending.Rational.Secant.eval_sub_factor
      expression.denominator x y
  rw [Ascending.Rational.Basic.RationalPolynomial.eval, Ascending.Rational.Basic.RationalPolynomial.eval,
    Ascending.Rational.Basic.RationalPolynomial.kernel]
  change numeratorX / denominatorX - numeratorY / denominatorY = _
  rw [Purelib.Data.Gaussian.Field.div_sub_div numeratorX numeratorY denominatorX denominatorY
    xDenominatorNonzero yDenominatorNonzero]
  have crossNumerator :
      numeratorX * denominatorY - numeratorY * denominatorX =
        (numeratorX - numeratorY) * denominatorY -
          numeratorY * (denominatorX - denominatorY) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
  have factoredNumerator :
      numeratorX * denominatorY - numeratorY * denominatorX =
      (x - y) *
        (numeratorKernel * denominatorY -
          numeratorY * denominatorKernel) := by
    calc
      numeratorX * denominatorY - numeratorY * denominatorX =
          (numeratorX - numeratorY) * denominatorY -
            numeratorY * (denominatorX - denominatorY) := crossNumerator
      _ = ((x - y) * numeratorKernel) * denominatorY -
            numeratorY * ((x - y) * denominatorKernel) := by
        rw [numeratorFactor, denominatorFactor]
      _ = (x - y) *
          (numeratorKernel * denominatorY -
            numeratorY * denominatorKernel) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1
  rw [factoredNumerator, Field.ExplicitField.div_eq_mul_inv,
    Field.ExplicitField.div_eq_mul_inv]
  exact Gaussian.Basic.mul_assoc _ _ _

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- At equal arguments, the rational secant kernel is the executable quotient-rule derivative. -/
theorem kernel_diagonal (expression :
  Ascending.Rational.Basic.RationalPolynomial) (x : Gaussian.Basic.Canonical) :
    expression.kernel x x = expression.derivativeEval x := by
  rw [Ascending.Rational.Basic.RationalPolynomial.kernel, Ascending.Rational.Basic.RationalPolynomial.derivativeEval,
    Ascending.Rational.Secant.polynomialKernel_diagonal, Ascending.Rational.Secant.polynomialKernel_diagonal]

end RationalPolynomial

end Purelib.RationalFunctions.Ascending.Rational.Basic

end
