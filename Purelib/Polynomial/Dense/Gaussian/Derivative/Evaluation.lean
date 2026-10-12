module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Traced normalized Gaussian-polynomial evaluation

This module runs dense Horner evaluation entirely through reduced Gaussian
rational working records.  Its trace lists every accumulator, its arithmetic
count is computed alongside the same recursion, and source-only recurrences
bound both the count and every intermediate component.  Erasing the final
working record gives the existing dense-polynomial evaluation exactly.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Evaluate the finite derivative polynomial at the displayed Gaussian point.

The result uses the existing normalized Gaussian record representation and ordinary dense Horner evaluation. -/
def derivativeEval (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Number :=
  Dense.Basic.DensePolynomial.eval (Dense.Derivative.derivative polynomial) point
end Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation

end

section
@[expose] public section

/-!
# Traced normalized Gaussian-polynomial evaluation

This module runs dense Horner evaluation entirely through reduced Gaussian
rational working records.  Its trace lists every accumulator, its arithmetic
count is computed alongside the same recursion, and source-only recurrences
bound both the count and every intermediate component.  Erasing the final
working record gives the existing dense-polynomial evaluation exactly.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Reading the derivative evaluation record gives the exact value of the finite derivative polynomial. -/
theorem value_derivativeEval (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    Gaussian.Basic.value (derivativeEval polynomial point) =
      (Dense.Derivative.derivative polynomial).eval point :=
  Dense.Gaussian.Evaluation.Horner.value_eval _ _
end Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation

end
