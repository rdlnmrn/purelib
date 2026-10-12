module
import Purelib.Approximation.Gaussian.Expression.Basic
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Projective.Basic

section
@[expose] public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

namespace Purelib.RationalFunctions.Approximation.Projective.Evaluate

open Purelib.Approximation in
open Purelib.Polynomial in
/-- Evaluate numerator and denominator as a pair of progressive Gaussian expressions.

Both expressions use the same input. The construction performs no affine division and requires no denominator-apartness
witness. -/
def evaluate (numerator denominator :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Approximation.Gaussian.Expression) : Gaussian.Projective.Basic.Pair :=
  { numerator := Approximation.Gaussian.Evaluation.Expression.polynomialExpression numerator input
    denominator := Approximation.Gaussian.Evaluation.Expression.polynomialExpression denominator input }

end Purelib.RationalFunctions.Approximation.Projective.Evaluate

end
