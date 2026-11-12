module
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.Power.Gaussian.Signed.Secant
public import Purelib.Data.Gaussian.Scale
public import Purelib.Polynomial.Laurent.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data

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

namespace Purelib.Polynomial.Laurent.Basic

open Purelib.Algebra.Power.Gaussian

/-- Evaluate the term's signed power at the displayed Gaussian input and scale by its Gaussian-rational coefficient. -/
def LaurentTerm.eval (term : Laurent.Basic.LaurentTerm) (x :
  Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  term.coefficient *
    (Signed.Secant.signedPower x term.exponent)

/-- Scale the finite signed-power secant kernel by the term's Gaussian-rational coefficient. -/
def LaurentTerm.kernel (term : Laurent.Basic.LaurentTerm) (x y
  : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  term.coefficient *
    (Signed.Secant.signedPowerKernel x y term.exponent)

/-- Scale the signed-power derivative value by the term's Gaussian-rational coefficient. -/
def LaurentTerm.derivativeEval (term :
  Laurent.Basic.LaurentTerm) (x : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  term.coefficient *
    (Signed.Secant.signedPowerDerivative x term.exponent)

/-- Evaluate and sum the finite displayed Laurent term list. -/
def LaurentPolynomial.eval (polynomial :
  Laurent.Basic.LaurentPolynomial)
    (x : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian (polynomial.terms.map fun term => term.eval x)

/-- Sum the finite termwise secant kernels at the two displayed Gaussian inputs. -/
def LaurentPolynomial.kernel (polynomial :
  Laurent.Basic.LaurentPolynomial)
    (x y : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian (polynomial.terms.map fun term => term.kernel x y)

/-- Sum the finite termwise derivative evaluations at the displayed input. -/
def LaurentPolynomial.derivativeEval (polynomial :
  Laurent.Basic.LaurentPolynomial)
    (x : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian (polynomial.terms.map fun term => term.derivativeEval x)

/-- The original expression is defined when every displayed negative power has a nonzero input.

Zero coefficients and cancellation do not remove a displayed term's guard. -/
def LaurentTerm.DefinedAt (term : LaurentTerm) (point : Gaussian.Basic.Canonical) : Prop :=
  term.exponent.negativeMagnitude ≠ 0 → point ≠ 0

/-- The original finite expression retains each of its displayed term domains. -/
def LaurentPolynomial.DefinedAt (polynomial : LaurentPolynomial)
    (point : Gaussian.Basic.Canonical) : Prop :=
  ∀ term ∈ polynomial.terms, term.DefinedAt point

/-- Every original Laurent expression is defined at a supplied nonzero point. -/
theorem LaurentPolynomial.definedAt_of_nonzero (polynomial : LaurentPolynomial)
    {point : Gaussian.Basic.Canonical} (nonzero : point ≠ 0) : polynomial.DefinedAt point := by
  intro term _ _
  exact nonzero

/-- Embed a rational coefficient in the original Gaussian Laurent term owner. -/
def LaurentTerm.ofRational (coefficient : Rat.Fraction.Rational)
    (exponent : Data.Int.Exponent) : LaurentTerm :=
  ⟨Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate coefficient, exponent⟩

/-- Rational coefficient inclusion preserves the original coordinate-scaling evaluator. -/
theorem LaurentTerm.eval_ofRational (coefficient : Rat.Fraction.Rational)
    (exponent : Data.Int.Exponent) (point : Gaussian.Basic.Canonical) :
    (LaurentTerm.ofRational coefficient exponent).eval point =
      Gaussian.Scale.scale coefficient
        (Signed.Secant.signedPower point exponent) := by
  exact Gaussian.Scale.scalar_mul_eq_scale coefficient _

/-- Rational coefficient inclusion retains the original finite secant kernel. -/
theorem LaurentTerm.kernel_ofRational (coefficient : Rat.Fraction.Rational)
    (exponent : Data.Int.Exponent) (left right : Gaussian.Basic.Canonical) :
    (LaurentTerm.ofRational coefficient exponent).kernel left right =
      Gaussian.Scale.scale coefficient
        (Signed.Secant.signedPowerKernel left right exponent) :=
  Gaussian.Scale.scalar_mul_eq_scale coefficient _

/-- Rational coefficient inclusion retains the original finite formal derivative value. -/
theorem LaurentTerm.derivativeEval_ofRational (coefficient : Rat.Fraction.Rational)
    (exponent : Data.Int.Exponent) (point : Gaussian.Basic.Canonical) :
    (LaurentTerm.ofRational coefficient exponent).derivativeEval point =
      Gaussian.Scale.scale coefficient
        (Signed.Secant.signedPowerDerivative point exponent) :=
  Gaussian.Scale.scalar_mul_eq_scale coefficient _

end Purelib.Polynomial.Laurent.Basic

end
