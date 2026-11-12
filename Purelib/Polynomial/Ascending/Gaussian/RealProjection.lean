module
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Polynomial.Dense.Rational.Evaluation.Ascending
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Rational real-axis projection of a finite Gaussian polynomial

The original ascending Gaussian coefficients supply their real coordinates,
which are retained in descending rational order. Evaluation at each rational
real-axis point reads the original Gaussian polynomial's real coordinate.
-/

public section

namespace Purelib.Polynomial.Ascending.Gaussian.RealProjection

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Read the original Gaussian coefficients' real coordinates in descending rational order. -/
@[expose] def dense (polynomial : CoefficientPolynomial) : Dense.Rational.Basic.CoordinatePolynomial :=
  ⟨(polynomial.coefficients.map Basic.Canonical.re).reverse⟩

/-- Gaussian Horner evaluation on the real axis has the scalar Horner reading of its real coefficients. -/
private theorem evalCoefficients (point : Fraction.Rational) : ∀ coefficients : List Basic.Canonical,
    (Evaluation.evalCoeffs coefficients (RationalEmbedding.realPoint point)).re =
      Ascending.Rational.Evaluation.scalarEvalCoefficients point (coefficients.map Basic.Canonical.re)
  | [] => rfl
  | first :: remaining => by
      rw [Evaluation.evalCoeffs_cons]
      change (first + RationalEmbedding.realPoint point *
        Evaluation.evalCoeffs remaining (RationalEmbedding.realPoint point)).re =
          first.re + point * Ascending.Rational.Evaluation.scalarEvalCoefficients point
            (remaining.map Basic.Canonical.re)
      rw [Basic.add_re, Basic.mul_re, RationalEmbedding.realPoint_re, RationalEmbedding.realPoint_im,
        evalCoefficients point remaining]
      ring1

/-- The original Gaussian evaluation's real coordinate equals the projected rational polynomial evaluation. -/
theorem eval (polynomial : CoefficientPolynomial) (point : Fraction.Rational) :
    (dense polynomial).eval point = (Evaluation.eval polynomial (RationalEmbedding.realPoint point)).re := by
  change Dense.Basic.DensePolynomial.evalCoeffs point (polynomial.coefficients.map Basic.Canonical.re).reverse = _
  rw [Dense.Rational.Evaluation.Ascending.eval_reverse]
  exact (evalCoefficients point polynomial.coefficients).symm

end Purelib.Polynomial.Ascending.Gaussian.RealProjection

end
