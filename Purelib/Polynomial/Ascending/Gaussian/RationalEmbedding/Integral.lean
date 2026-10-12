module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Antiderivative
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Basic
import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Evaluation
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Integral

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

namespace Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Integral

/-- The two existing finite integration kernels compute exactly the same
Gaussian value after the structural coefficient translation. -/
theorem definiteIntegral_ofRational (polynomial
  : Ascending.Rational.Basic.CoefficientPolynomial)
    (start finish : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.RationalEmbedding.Basic.ofRational polynomial)
      start finish =
      Ascending.Rational.Integral.definiteIntegral polynomial start finish := by
  unfold Ascending.Gaussian.Integral.definiteIntegral Ascending.Rational.Integral.definiteIntegral
  rw [Ascending.Gaussian.RationalEmbedding.Antiderivative.antiderivative_ofRational,
    Ascending.Gaussian.RationalEmbedding.Evaluation.eval_ofRational,
    Ascending.Gaussian.RationalEmbedding.Evaluation.eval_ofRational]

end Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Integral

end
