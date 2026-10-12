module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Expression.Basic
public import Purelib.Approximation.Gaussian.Projective.Exact
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Approximation.Projective.Evaluate

section
@[expose] public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

namespace Purelib.RationalFunctions.Approximation.Projective.Exact

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Projective evaluation at an exact Gaussian input retains both exact polynomial evaluations.

The numerator and denominator expressions each carry their operational exactness certificate. No denominator-apartness
decision is needed for this paired result. -/
def evaluate_exact (numerator denominator :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Gaussian.Basic.Canonical) :
    Gaussian.Projective.Exact.ExactPair
      (Approximation.Projective.Evaluate.evaluate numerator denominator
        (Approximation.Gaussian.Expression.exact input))
      (numerator.eval input) (denominator.eval input) :=
  { numeratorExact := Approximation.Gaussian.Evaluation.Expression.polynomialExpression_exact numerator input
    denominatorExact := Approximation.Gaussian.Evaluation.Expression.polynomialExpression_exact denominator input }

end Purelib.RationalFunctions.Approximation.Projective.Exact

end
