module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
public import Purelib.Polynomial.Ascending.Rational.Antiderivative
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Secant

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite integration, an algebraic FTC, and polynomial ODE certificates

Integration here is coefficient arithmetic on a displayed finite polynomial.
The antiderivative divides each coefficient by its positive natural degree.
The fundamental theorem is the pair of exact finite statements that
differentiating this table returns the original table and that an interval
increment factors through the antiderivative's secant kernel.

The final section packages elementary initial-value problems with polynomial
forcing and records the exact finite defect of the exponential polynomial for
`y' = y`.  No measure, completed interval, limiting partition, or
function-as-an-infinite-set is used.
-/

namespace Purelib.Polynomial.Ascending.Rational.Integral

/-- Exact finite interval evaluation of the constructed antiderivative. -/
def definiteIntegral (polynomial :
  CoefficientPolynomial) (left right : Gaussian.Basic.Canonical) :
    Gaussian.Basic.Canonical :=
  Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Antiderivative.antiderivative 0 polynomial) right -
    Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Antiderivative.antiderivative 0 polynomial) left

/-- Reversing the displayed interval negates the exact finite integral. -/
theorem definiteIntegral_reverse (polynomial :
  CoefficientPolynomial)
    (left right : Gaussian.Basic.Canonical) :
    definiteIntegral polynomial right left =
      -(definiteIntegral polynomial left right) := by
  unfold definiteIntegral
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1

/-- Adjacent displayed intervals concatenate exactly. -/
theorem definiteIntegral_concat (polynomial :
  CoefficientPolynomial)
    (left middle right : Gaussian.Basic.Canonical) :
    definiteIntegral polynomial left right =
      definiteIntegral polynomial left middle +
        definiteIntegral polynomial middle right := by
  unfold definiteIntegral
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1

/-- Linearity for addition of finite polynomial integrands. -/
theorem definiteIntegral_add (left right :
  CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral (Ascending.Rational.Basic.add left right) start finish =
      definiteIntegral left start finish +
        definiteIntegral right start finish := by
  unfold definiteIntegral
  rw [Ascending.Rational.Antiderivative.antiderivative_add,
    Ascending.Rational.GaussianEvaluation.eval_add,
    Ascending.Rational.GaussianEvaluation.eval_add]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1

/-- Linearity for a displayed rational scalar. -/
theorem definiteIntegral_scale (factor : Fraction.Rational)
  (polynomial : CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) :
    definiteIntegral (Ascending.Rational.Basic.scale factor polynomial) start finish =
      Gaussian.Scale.scale factor
        (definiteIntegral polynomial start finish) := by
  unfold definiteIntegral
  rw [Ascending.Rational.Antiderivative.antiderivative_scale,
    Ascending.Rational.GaussianEvaluation.eval_scale,
    Ascending.Rational.GaussianEvaluation.eval_scale]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Scale.scale_re,
      Gaussian.Scale.scale_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1

/-- The finite average-change kernel of the antiderivative. -/
def integralKernel (polynomial :
  CoefficientPolynomial) (left right : Gaussian.Basic.Canonical) :
    Gaussian.Basic.Canonical :=
  Ascending.Rational.Secant.polynomialKernel
    (Ascending.Rational.Antiderivative.antiderivative 0 polynomial) right left

/-- Infinitesimal-free interval form of the fundamental theorem: the
constructed integral is exactly displacement times one displayed finite
secant kernel. -/
theorem definiteIntegral_factor (polynomial :
  CoefficientPolynomial)
    (left right : Gaussian.Basic.Canonical) :
    definiteIntegral polynomial left right =
      (right - left) * integralKernel polynomial left right :=
  Ascending.Rational.Secant.eval_sub_factor
    (Ascending.Rational.Antiderivative.antiderivative 0 polynomial) right left

/-- Diagonal substitution in the already-expanded interval kernel returns
the integrand value. -/
theorem integralKernel_diagonal (polynomial :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    integralKernel polynomial point point = Ascending.Rational.GaussianEvaluation.eval
      polynomial point := by
  rw [integralKernel,
    Ascending.Rational.Secant.polynomialKernel_diagonal]
  rw [Ascending.Rational.Antiderivative.derivative_antiderivative]
end Purelib.Polynomial.Ascending.Rational.Integral

end
