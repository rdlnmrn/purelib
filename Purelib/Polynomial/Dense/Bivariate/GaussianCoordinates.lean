module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Bivariate.Basic (DenseBivariate)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Algebra.Field

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.GaussianCoordinates
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-! ## Gaussian coordinate construction -/

/-- One Gaussian Horner step performed on a pair of rational bivariate coordinate polynomials. -/
def coordinateStep (xVariable yVariable :
  DenseBivariate Fraction.Rational)
    (state : DenseBivariate Fraction.Rational × DenseBivariate
      Fraction.Rational)
    (coefficient : Gaussian.Basic.Canonical) :
    DenseBivariate Fraction.Rational × DenseBivariate Fraction.Rational :=
  (Dense.Bivariate.Basic.add (Dense.Bivariate.Basic.sub (Dense.Bivariate.Basic.mul state.1 xVariable)
    (Dense.Bivariate.Basic.mul state.2 yVariable))
      (Dense.Bivariate.Basic.constant coefficient.re),
    Dense.Bivariate.Basic.add (Dense.Bivariate.Basic.add (Dense.Bivariate.Basic.mul state.1 yVariable)
      (Dense.Bivariate.Basic.mul state.2 xVariable))
      (Dense.Bivariate.Basic.constant coefficient.im))

/-- Compute both rational bivariate coordinate polynomials by folding the normalized Gaussian coefficient table.

The supplied bivariate variables determine the real and imaginary argument coordinates; both accumulators start at zero.
-/
def coordinatePolynomials (p :
  CoefficientPolynomial)
    (xVariable yVariable : DenseBivariate Fraction.Rational) :
    DenseBivariate Fraction.Rational × DenseBivariate Fraction.Rational :=
  p.normalize.coeffs.foldl (coordinateStep xVariable yVariable)
    (Dense.Bivariate.Basic.zero, Dense.Bivariate.Basic.zero)

/-- `Y` is outer and `X` is inner. -/
def verticalCoordinates (p :
  CoefficientPolynomial) :
    DenseBivariate Fraction.Rational × DenseBivariate Fraction.Rational :=
  coordinatePolynomials p Dense.Bivariate.Basic.innerX Dense.Bivariate.Basic.outerX

/-- `X` is outer and `Y` is inner. -/
def horizontalCoordinates (p :
  CoefficientPolynomial) :
    DenseBivariate Fraction.Rational × DenseBivariate Fraction.Rational :=
  coordinatePolynomials p Dense.Bivariate.Basic.outerX Dense.Bivariate.Basic.innerX

/-- The bivariate coordinate fold evaluates to the real and imaginary coordinates of the same scalar Gaussian Horner
fold. -/
private theorem eval_coordinateFold_from
    (xVariable yVariable : DenseBivariate Fraction.Rational)
    (outer inner x y : Fraction.Rational)
    (xEval : Dense.Bivariate.Basic.eval xVariable outer inner = x)
    (yEval : Dense.Bivariate.Basic.eval yVariable outer inner = y)
    (coefficients : List Gaussian.Basic.Canonical)
    (real imag : DenseBivariate Fraction.Rational) (z : Gaussian.Basic.Canonical)
    (realEval : Dense.Bivariate.Basic.eval real outer inner = z.re)
    (imagEval : Dense.Bivariate.Basic.eval imag outer inner = z.im) :
    let result := coefficients.foldl
      (coordinateStep xVariable yVariable) (real, imag)
    Dense.Bivariate.Basic.eval result.1 outer inner =
        (coefficients.foldl
          (fun value coefficient => value * ⟨x, y⟩ + coefficient) z).re ∧
      Dense.Bivariate.Basic.eval result.2 outer inner =
        (coefficients.foldl
          (fun value coefficient => value * ⟨x, y⟩ + coefficient) z).im := by
  induction coefficients generalizing real imag z with
  | nil => exact ⟨realEval, imagEval⟩
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · simp only [Dense.Bivariate.Basic.eval_add, Dense.Bivariate.Basic.eval_sub, Dense.Bivariate.Basic.eval_mul,
          Dense.Bivariate.Basic.eval_constant, xEval, yEval, realEval, imagEval, Gaussian.Basic.mul_re,
            Gaussian.Basic.add_re, -eq_self, -iff_self]
        rfl
      · simp only [Dense.Bivariate.Basic.eval_add, Dense.Bivariate.Basic.eval_mul, Dense.Bivariate.Basic.eval_constant,
          xEval, yEval, realEval, imagEval, Gaussian.Basic.mul_im, Gaussian.Basic.add_im, -eq_self, -iff_self]
        rfl

/-- The vertical coordinate pair evaluates to the original Gaussian value, with imaginary variable outermost. -/
theorem eval_verticalCoordinates (p :
  CoefficientPolynomial) (x y : Fraction.Rational) :
    Dense.Bivariate.Basic.eval (verticalCoordinates p).1 y x = (p.eval ⟨x, y⟩).re ∧
      Dense.Bivariate.Basic.eval (verticalCoordinates p).2 y x = (p.eval ⟨x, y⟩).im
        := by
  rw [← DensePolynomial.eval_normalize p ⟨x, y⟩]
  have evaluated := eval_coordinateFold_from Dense.Bivariate.Basic.innerX
    Dense.Bivariate.Basic.outerX y x x y
    (Dense.Bivariate.Basic.eval_innerX y x) (Dense.Bivariate.Basic.eval_outerX y x)
    p.normalize.coeffs Dense.Bivariate.Basic.zero Dense.Bivariate.Basic.zero 0
    (Dense.Bivariate.Basic.eval_zero y x) (Dense.Bivariate.Basic.eval_zero y x)
  simpa only [verticalCoordinates,
    coordinatePolynomials, Dense.Bivariate.Basic.eval,
    DensePolynomial.eval, DensePolynomial.evalCoeffs, Gaussian.Basic.zero_re,
    Gaussian.Basic.zero_im, -eq_self, -iff_self] using evaluated

/-- The horizontal coordinate pair evaluates to the original Gaussian value, with real variable outermost. -/
theorem eval_horizontalCoordinates (p :
  CoefficientPolynomial) (x y : Fraction.Rational) :
    Dense.Bivariate.Basic.eval (horizontalCoordinates p).1 x y = (p.eval ⟨x, y⟩).re
      ∧
      Dense.Bivariate.Basic.eval (horizontalCoordinates p).2 x y = (p.eval ⟨x,
        y⟩).im := by
  rw [← DensePolynomial.eval_normalize p ⟨x, y⟩]
  have evaluated := eval_coordinateFold_from Dense.Bivariate.Basic.outerX
    Dense.Bivariate.Basic.innerX x y x y
    (Dense.Bivariate.Basic.eval_outerX x y) (Dense.Bivariate.Basic.eval_innerX x y)
    p.normalize.coeffs Dense.Bivariate.Basic.zero Dense.Bivariate.Basic.zero 0
    (Dense.Bivariate.Basic.eval_zero x y) (Dense.Bivariate.Basic.eval_zero x y)
  simpa only [horizontalCoordinates,
    coordinatePolynomials, Dense.Bivariate.Basic.eval,
    DensePolynomial.eval, DensePolynomial.evalCoeffs, Gaussian.Basic.zero_re,
    Gaussian.Basic.zero_im, -eq_self, -iff_self] using evaluated
end Purelib.Polynomial.Dense.Bivariate.GaussianCoordinates

end
