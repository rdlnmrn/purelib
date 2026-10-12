module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Basic
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Newton update using the two normalized Horner evaluations directly. -/
def newtonCenter (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Number :=
  Gaussian.Basic.sub
    (Gaussian.Basic.ofGaussian point)
    (Gaussian.Field.div (Dense.Basic.DensePolynomial.eval polynomial point)
      (Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point))
end Purelib.Polynomial.Dense.Gaussian.Newton.Basic

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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Basic
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Reading the normalized Newton update gives point minus polynomial value divided by derivative value. -/
theorem value_newtonCenter (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    Gaussian.Basic.value (newtonCenter polynomial point) =
      point - polynomial.eval point /
        (Dense.Derivative.derivative polynomial).eval point := by
  rw [newtonCenter, Gaussian.Basic.value_sub,
    Gaussian.Basic.value_ofGaussian,
    Gaussian.Field.value_div, Dense.Gaussian.Evaluation.Horner.value_eval,
      Dense.Gaussian.Derivative.Evaluation.value_derivativeEval]
end Purelib.Polynomial.Dense.Gaussian.Newton.Basic

end
