module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Rational.Pair.Product
public import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

section
@[expose] public section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

namespace Purelib.RationalFunctions.Path.Polynomial

section
open Purelib.Data
open Purelib.Polynomial
/-- Form the real coordinate polynomial of the numerator times the conjugate denominator along an affine line.

The coordinate is computed from the two real and imaginary polynomial pairs. Division is avoided; a positive denominator
quadrance later recovers the quotient's direction. -/
def quotientPathReal
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) : (DensePolynomial Rat.Fraction.Rational) :=
  Dense.Rational.Pair.Product.productReal
    (Dense.Gaussian.Path.Components.pathReal numerator origin direction)
    (Dense.Gaussian.Path.Components.pathImag numerator origin direction)
    (Dense.Gaussian.Path.Components.pathReal denominator origin direction)
    (-(Dense.Gaussian.Path.Components.pathImag denominator origin direction))

/-- Form the imaginary coordinate polynomial of the numerator times the conjugate denominator along an affine line.

The coordinate subtracts the numerator-real times denominator-imaginary product from the numerator-imaginary times
denominator-real product. -/
def quotientPathImag
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) : (DensePolynomial Rat.Fraction.Rational) :=
  Dense.Rational.Pair.Product.productImag
    (Dense.Gaussian.Path.Components.pathReal numerator origin direction)
    (Dense.Gaussian.Path.Components.pathImag numerator origin direction)
    (Dense.Gaussian.Path.Components.pathReal denominator origin direction)
    (-(Dense.Gaussian.Path.Components.pathImag denominator origin direction))

section
open Purelib.Geometry
open Purelib.RationalFunctions
/-- The real coordinate polynomial evaluates to the sum of the two matching component products. -/
@[simp] theorem eval_quotientPathReal
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) (t : Rat.Fraction.Rational) :
    (quotientPathReal numerator denominator origin direction).eval t =
      (numerator.eval (Rational.Affine.line origin direction t)).re *
          (denominator.eval (Rational.Affine.line origin direction t)).re +
        (numerator.eval (Rational.Affine.line origin direction t)).im *
          (denominator.eval (Rational.Affine.line origin direction t)).im := by
  simp only [quotientPathReal, Dense.Rational.Pair.Product.eval_productReal,
    DensePolynomial.eval_neg, Dense.Gaussian.Path.Components.eval_pathReal,
    Dense.Gaussian.Path.Components.eval_pathImag]
  ring1

/-- The imaginary coordinate polynomial evaluates to the difference of the two crossed component products. -/
@[simp] theorem eval_quotientPathImag
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) (t : Rat.Fraction.Rational) :
    (quotientPathImag numerator denominator origin direction).eval t =
      (numerator.eval (Rational.Affine.line origin direction t)).im *
          (denominator.eval (Rational.Affine.line origin direction t)).re -
        (numerator.eval (Rational.Affine.line origin direction t)).re *
          (denominator.eval (Rational.Affine.line origin direction t)).im := by
  simp only [quotientPathImag, Dense.Rational.Pair.Product.eval_productImag,
    DensePolynomial.eval_neg, Dense.Gaussian.Path.Components.eval_pathReal,
    Dense.Gaussian.Path.Components.eval_pathImag]
  ring1

end

open Purelib.RationalFunctions in
/-- Package the denominator-cleared coordinate polynomials and an oriented rational parameter interval.

The endpoints retain the supplied start and stop order. No nonzero-denominator witness is required to construct this
polynomial edge. -/
def quotientEdge
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) (start stop : Rat.Fraction.Rational) :
      Dense.Rational.Pair.Path.Basic.PolynomialEdge :=
  { realPart := quotientPathReal numerator denominator origin direction
    imagPart := quotientPathImag numerator denominator origin direction
    start := start
    stop := stop }
end

end Purelib.RationalFunctions.Path.Polynomial

end
