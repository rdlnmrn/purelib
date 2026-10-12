module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic
public import Purelib.Polynomial.Ascending.Rational.Antiderivative
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Antiderivative

section Antiderivative

/-- Embedding rational coefficients commutes with integration at matching positive degree offsets. -/
theorem
  antiderivativeCoefficients_map
  : ∀ (offset : Nat) (coefficients : List Fraction.Rational),
    Ascending.Gaussian.Antiderivative.antiderivativeCoefficients offset (coefficients.map
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate) =
      (Ascending.Rational.Antiderivative.integrateCoefficients (offset + 1) coefficients).map
        Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate
  | _, [] => rfl
  | offset, head :: tail => by
      rw [List.map_cons, Ascending.Gaussian.Antiderivative.antiderivativeCoefficients,
        Ascending.Rational.Antiderivative.integrateCoefficients, List.map_cons,

          antiderivativeCoefficients_map
          (offset + 1) tail,
        Data.Gaussian.RationalEmbedding.coordinate_div_nat head (offset + 1) (Nat.succ_pos offset)]

end Antiderivative

/-- The zero-constant Gaussian antiderivative of an embedded rational table equals the embedded rational antiderivative.
-/
theorem antiderivative_ofRational
  (polynomial : Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Gaussian.Antiderivative.antiderivative (Ascending.Gaussian.RationalEmbedding.Basic.ofRational polynomial)
      =
      Ascending.Gaussian.RationalEmbedding.Basic.ofRational (Ascending.Rational.Antiderivative.antiderivative 0
        polynomial) := by
  change (⟨0 :: Ascending.Gaussian.Antiderivative.antiderivativeCoefficients 0
      (polynomial.coefficients.map Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate)⟩ :
        CoefficientPolynomial) =
    ⟨(0 :: Ascending.Rational.Antiderivative.integrateCoefficients 1 polynomial.coefficients).map
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate⟩
  rw [antiderivativeCoefficients_map]
  rfl
end Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Antiderivative

end
