module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.Jump
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
public import Purelib.RationalFunctions.Path.Polynomial

open Purelib.Data.Gaussian.Basic (Canonical)
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

namespace Purelib.RationalFunctions.Winding.Path.Correction

open Purelib.Data in
open Purelib.Polynomial in
/-- Compute the doubled quotient product-rule endpoint correction at a Gaussian vertex.

The finite sign jump uses the imaginary numerator of numerator times conjugate denominator, multiplied by the two
relevant imaginary-coordinate factors. -/
def vertexQuotientCorrection2
    (numerator denominator : CoefficientPolynomial) (z :
      Canonical) : Nat :=
  let numeratorValue := numerator.eval z
  let denominatorValue := denominator.eval z
  Rat.Sign.Jump.signJump 1
    ((numeratorValue.im * denominatorValue.re -
        numeratorValue.re * denominatorValue.im) *
      (numeratorValue.im * (-denominatorValue.im)))

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Evaluate the quotient vertex correction at the displayed affine-line parameter. -/
def lineQuotientCorrection2
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) (t : Rat.Fraction.Rational) : Nat :=
  vertexQuotientCorrection2 numerator denominator
    (Rational.Affine.line origin direction t)

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The polynomial product-rule endpoint correction equals the displayed affine-line quotient correction.

The factors are the numerator imaginary path coordinate and the negated denominator imaginary path coordinate; their
product correction uses the quotient imaginary coordinate. -/
theorem auxiliaryEndpointCorrection2_quotient
    (numerator denominator : CoefficientPolynomial)
    (origin direction : Canonical) (t : Rat.Fraction.Rational) :
    Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
        (Dense.Gaussian.Path.Components.pathImag numerator origin direction)
        (-(Dense.Gaussian.Path.Components.pathImag denominator origin direction))
        (Path.Polynomial.quotientPathImag numerator denominator origin direction) t =
      lineQuotientCorrection2 numerator denominator origin direction t := by
  unfold Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
    lineQuotientCorrection2 vertexQuotientCorrection2
  simp only [Path.Polynomial.eval_quotientPathImag, Dense.Gaussian.Path.Components.eval_pathImag,
    Dense.Basic.DensePolynomial.eval_neg, -eq_self, -iff_self]
  rfl
end Purelib.RationalFunctions.Winding.Path.Correction

end
