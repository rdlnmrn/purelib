module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Reading the canonical value of Gaussian coefficient evaluation preserves the result. -/
theorem value_evalCoeffs (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) :
    Gaussian.Basic.value (DensePolynomial.evalCoeffs point coefficients) =
      DensePolynomial.evalCoeffs point coefficients := by
  rfl
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Reading the canonical value of Gaussian polynomial evaluation preserves its result. -/
theorem value_eval (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    Gaussian.Basic.value (DensePolynomial.eval polynomial point) =
      polynomial.eval point := by
  exact value_evalCoeffs point polynomial.coeffs
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner
open Purelib.Algebra.Polynomial.DensePolynomial

/-- The normalized Horner fold reads back to the scalar fold from the same initial value. -/
theorem value_evalCoeffsFrom (point accumulator :
  Gaussian.Basic.Number)
    (coefficients : List Gaussian.Basic.Canonical) :
    Gaussian.Basic.value
        (Dense.Evaluation.evalCoeffsFrom point accumulator coefficients) =
      coefficients.foldl
        (fun current coefficient =>
          current * Gaussian.Basic.value point + coefficient)
        (Gaussian.Basic.value accumulator) := by
  rfl
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner
open Purelib.Algebra.Polynomial.DensePolynomial

/-- One normalized Horner clause. -/
theorem value_step (point accumulator :
  Gaussian.Basic.Number)
    (coefficient : Gaussian.Basic.Canonical) :
    Gaussian.Basic.value (Dense.Evaluation.step point accumulator coefficient) =
      Gaussian.Basic.value accumulator *
          Gaussian.Basic.value point + coefficient := by
  rfl
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner

end
