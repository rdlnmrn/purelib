module
public import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Embedding finite rational coefficient tables in Gaussian polynomials

This is a structural map on finite lists, with evaluation, differentiation
and integration compatibility proved from the coefficient recursions.  It
does not identify polynomials by testing them on an infinite carrier.

The rational-side imports supply the existing finite coefficient calculus;
the Gaussian side supplies direct coefficient algebra.  No analytic
polynomial or completed scalar field is used.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic

/-- Embed the displayed rational coefficients, retaining their order and
length, including explicit trailing zero coefficients. -/
def ofRational (polynomial :
  Ascending.Rational.Basic.CoefficientPolynomial) : Polynomial.Ascending.Gaussian.CoefficientPolynomial :=
  ⟨polynomial.coefficients.map Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate⟩
end Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic

end
