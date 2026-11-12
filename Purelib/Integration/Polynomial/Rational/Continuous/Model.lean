module
public import Purelib.Integration.Polynomial.Rational.Continuous
public import Purelib.Integration.Polynomial.Gaussian.Continuous
public import Purelib.Integration.Polynomial.Rational.Cell.Basic
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic
public import Purelib.Polynomial.Ascending.Rational.Evaluation
import Purelib.Polynomial.Dense.Rational.Evaluation.Ascending
import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Integral
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Data.List.Reverse

/-!
# Finite rational polynomial integration and original Gaussian models

The retained descending rational coefficient list is reversed once into the
original ascending table, then embedded into the Gaussian coefficient owner.
Exact finite Horner readbacks relate both original polynomial evaluators.
-/

public section

namespace Purelib.Integration.Polynomial.Rational.Continuous.Model

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Integration.Polynomial.Gaussian

/-- Retain the original descending rational coefficients in ascending order. -/
@[expose] def ascending (polynomial : Dense.Rational.Basic.CoordinatePolynomial) :
    Ascending.Rational.Basic.CoefficientPolynomial := ⟨polynomial.coeffs.reverse⟩

/-- Embed the same retained rational coefficients in the original Gaussian polynomial owner. -/
@[expose] def gaussian (polynomial : Dense.Rational.Basic.CoordinatePolynomial) :
    Ascending.Gaussian.CoefficientPolynomial :=
  Ascending.Gaussian.RationalEmbedding.Basic.ofRational (ascending polynomial)

/-- The original rational-coefficient unit cell for the retained ascending table. -/
@[expose] def rationalCell (polynomial : Dense.Rational.Basic.CoordinatePolynomial) : Cell.Basic.CellModel :=
  Cell.Basic.CellModel.exact 0 1 (ascending polynomial)

/-- The original dense rational evaluation equals the scalar reading of the retained ascending coefficients. -/
theorem ascending_eval (polynomial : Dense.Rational.Basic.CoordinatePolynomial) (point : Fraction.Rational) :
    polynomial.eval point = Ascending.Rational.Evaluation.scalarEval point (ascending polynomial) := by
  change Dense.Basic.DensePolynomial.evalCoeffs point polynomial.coeffs =
    Ascending.Rational.Evaluation.scalarEvalCoefficients point polynomial.coeffs.reverse
  have readback := Dense.Rational.Evaluation.Ascending.eval_reverse point polynomial.coeffs.reverse
  rw [Purelib.Data.List.Reverse.reverse_reverse] at readback
  exact readback

/-- Gaussian evaluation of the same original finite coefficient list preserves every rational point reading. -/
theorem gaussian_source (polynomial : Dense.Rational.Basic.CoordinatePolynomial) (point : Fraction.Rational) :
    Gaussian.Continuous.source (gaussian polynomial) point = polynomial.eval point := by
  unfold Gaussian.Continuous.source gaussian
  rw [Ascending.Gaussian.RationalEmbedding.Evaluation.eval_ofRational]
  change (Ascending.Rational.GaussianEvaluation.eval (ascending polynomial)
    (RationalEmbedding.ComplexLog.scalar point)).re = polynomial.eval point
  rw [Ascending.Rational.GaussianEvaluation.eval_scalar]
  change Ascending.Rational.Evaluation.scalarEval point (ascending polynomial) = polynomial.eval point
  exact (ascending_eval polynomial point).symm

/-- The original Gaussian and rational coefficient cells have exactly the same integral sample. -/
theorem gaussian_cell_sample (polynomial : Dense.Rational.Basic.CoordinatePolynomial) :
    (Gaussian.Continuous.model (gaussian polynomial)).integralSample = (rationalCell polynomial).integralSample := by
  rw [Gaussian.Continuous.model, Gaussian.Cell.Basic.CellModel.exact_integralSample,
    rationalCell, Cell.Basic.CellModel.exact_integralSample]
  rw [gaussian, Ascending.Gaussian.RationalEmbedding.Integral.definiteIntegral_ofRational]

/-- Every computed rational polynomial enclosure contains the original Gaussian model's exact integral sample.

The descending rational coefficients, their ascending Gaussian embedding and
the original Gaussian unit cell remain visible. The proof uses the actual
source frontier and its finite polynomial primitive comparison for every
coefficient list, including constants and higher degrees. -/
theorem integral_contains (polynomial : Dense.Rational.Basic.CoordinatePolynomial)
    (request : Purelib.Approximation.AccuracyRequest) :
    (integralBound (integrate polynomial request).frontier.cells).Contains
      (Gaussian.Continuous.model (gaussian polynomial)).integralSample.re :=
  Gaussian.Continuous.model_sample_contains_of_eq (gaussian polynomial) (integrate polynomial request).frontier
    (fun point _ _ => (gaussian_source polynomial point).symm)

/-- Every computed rational polynomial enclosure also contains the original rational cell's exact integral sample. -/
theorem rational_cell_contains (polynomial : Dense.Rational.Basic.CoordinatePolynomial)
    (request : Purelib.Approximation.AccuracyRequest) :
    (integralBound (integrate polynomial request).frontier.cells).Contains
      (rationalCell polynomial).integralSample.re := by
  have result := integral_contains polynomial request
  rw [gaussian_cell_sample] at result
  exact result

end Purelib.Integration.Polynomial.Rational.Continuous.Model

end
