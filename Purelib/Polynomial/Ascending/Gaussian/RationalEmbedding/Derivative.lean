module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Derivative
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Data.Gaussian.Basic

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

namespace Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Derivative

section RationalEmbedding

/-- Embedding rational coefficients commutes with natural degree weighting. -/
theorem derivativeFrom_map :
  ∀ (degree : Nat) (coefficients : List Fraction.Rational),
    Ascending.Gaussian.Derivative.derivativeFrom degree (coefficients.map
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate) =
      (Ascending.Rational.Derivative.derivativeFrom degree coefficients).map
        Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate
  | _, [] => rfl
  | degree, head :: tail => by
      rw [List.map_cons, Ascending.Gaussian.Derivative.derivativeFrom, Ascending.Rational.Derivative.derivativeFrom,
        List.map_cons,
          derivativeFrom_map
          (degree + 1) tail,
        Data.Gaussian.RationalEmbedding.coordinate_mul,
          Data.Gaussian.RationalEmbedding.coordinate_natCast]
end RationalEmbedding

/-- Differentiating an embedded rational polynomial equals embedding its rational derivative table. -/
theorem derivative_ofRational (polynomial :
  Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Gaussian.Derivative.derivative (Ascending.Gaussian.RationalEmbedding.Basic.ofRational polynomial) =
      Ascending.Gaussian.RationalEmbedding.Basic.ofRational (Ascending.Rational.Derivative.derivative polynomial) := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil => rfl
      | cons head tail =>
          change (⟨Ascending.Gaussian.Derivative.derivativeFrom 1 (tail.map
            Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate)⟩ : CoefficientPolynomial) =
            ⟨(Ascending.Rational.Derivative.derivativeFrom 1 tail).map
              Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate⟩
          rw [derivativeFrom_map]
end Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Derivative

end
