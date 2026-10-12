module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Polynomial.Ascending.Rational.Basic renaming CoefficientPolynomial -> RationalPolynomial

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

namespace Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Evaluation

section RationalEmbedding

/-- Gaussian evaluation of an embedded rational table agrees with direct Gaussian evaluation of its rational
coefficients. -/
theorem evalCoeffs_map
  (input : Gaussian.Basic.Canonical) : ∀ coefficients : List Fraction.Rational,
    Ascending.Gaussian.Evaluation.evalCoeffs (coefficients.map
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate) input =
      Ascending.Rational.GaussianEvaluation.evalCoefficients input coefficients
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, Ascending.Gaussian.Evaluation.evalCoeffs_cons,
        Ascending.Rational.GaussianEvaluation.evalCoefficients_cons,
        evalCoeffs_map input tail,
          Purelib.Data.Gaussian.Scale.coordinate_scale_one]

/-- Reading an embedded table embeds the original rational coefficient, including zero beyond the table. -/
theorem coefficientList_map
  : ∀ (coefficients : List Fraction.Rational) (degree : Nat),
    Ascending.Gaussian.Coefficient.coefficientList (coefficients.map
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate) degree =
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate (Ascending.Rational.Basic.coefficientCoefficients
        coefficients degree)
  | [], degree => by
      rw [List.map_nil, Ascending.Gaussian.Coefficient.coefficientList,
        Ascending.Rational.Basic.coefficientCoefficients_nil]
      rfl
  | _ :: _, 0 => rfl
  | _ :: tail, degree + 1 =>
    coefficientList_map tail degree
end RationalEmbedding

/-- Embedding the rational coefficient table preserves its Gaussian value. -/
theorem eval_ofRational (polynomial :
  RationalPolynomial) (input : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.RationalEmbedding.Basic.ofRational polynomial) input =
      Ascending.Rational.GaussianEvaluation.eval polynomial input :=
  evalCoeffs_map input polynomial.coefficients

/-- Each coefficient of the embedded polynomial is the corresponding embedded rational coefficient. -/
theorem coefficient_ofRational (polynomial :
  RationalPolynomial) (degree : Nat) :
    Ascending.Gaussian.Coefficient.coefficient (Ascending.Gaussian.RationalEmbedding.Basic.ofRational polynomial) degree
      =
      Gaussian.RationalEmbedding.PolynomialEmbedding.coordinate (Ascending.Rational.Basic.coefficient polynomial degree)
        :=
  coefficientList_map polynomial.coefficients degree

/-- The structural rational embedding preserves coefficientwise equality. -/
theorem ofRational_coefficientwise {left right
  : RationalPolynomial}
    (equal : Ascending.Rational.Coefficientwise.CoefficientwiseEqual left right) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (Ascending.Gaussian.RationalEmbedding.Basic.ofRational left)
      (Ascending.Gaussian.RationalEmbedding.Basic.ofRational right) := by
  intro degree
  rw [coefficient_ofRational,
    coefficient_ofRational, equal degree]
end Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Evaluation

end
