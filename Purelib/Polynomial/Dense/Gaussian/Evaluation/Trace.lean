module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Resource
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Audited arithmetic clauses executed by exactly the same accumulator
recursion. -/
def stepsFrom (point : Gaussian.Basic.Number) :
    Gaussian.Basic.Number → List Gaussian.Basic.Canonical → Nat
  | _, [] => 0
  | accumulator, coefficient :: remaining =>
      let product := Gaussian.Basic.mul accumulator point
      Gaussian.Resource.mulSteps accumulator point +
        Gaussian.Resource.addSteps product
          (Gaussian.Basic.ofGaussian coefficient) +
        stepsFrom point (Dense.Evaluation.step point accumulator
          coefficient) remaining
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Count the executed arithmetic clauses of normalized Horner evaluation from zero.

The recursion uses the displayed point and coefficients, including the intermediate normalized multiplication results.
-/
def steps (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) : Nat :=
  stepsFrom (Gaussian.Basic.ofGaussian point)
    (Gaussian.Basic.ofGaussian 0) coefficients
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
open Purelib.Algebra.Polynomial.DensePolynomial

/-! ## Executed trace and arithmetic count -/

/-- Every accumulator visited by the normalized Horner recursion, including
the initial and final accumulators. -/
def traceFrom (point : Gaussian.Basic.Number) :
    Gaussian.Basic.Number → List Gaussian.Basic.Canonical → List Gaussian.Basic.Number
  | accumulator, [] => [accumulator]
  | accumulator, coefficient :: remaining =>
      accumulator ::
        traceFrom point (Dense.Evaluation.step point accumulator
          coefficient) remaining
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
open Purelib.Algebra.Polynomial.DensePolynomial

/-- List every normalized Horner accumulator starting from zero.

The trace includes both the initial zero and final evaluated accumulator. -/
def trace (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) : List Gaussian.Basic.Number :=
  traceFrom (Gaussian.Basic.ofGaussian point)
    (Gaussian.Basic.ofGaussian 0) coefficients
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace

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

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
open Purelib.Algebra.Polynomial.DensePolynomial

/-- A Horner trace contains one more accumulator than the number of coefficients. -/
@[simp] theorem traceFrom_length (point accumulator :
  Gaussian.Basic.Number)
    (coefficients : List Gaussian.Basic.Canonical) :
    (traceFrom point accumulator coefficients).length =
      coefficients.length + 1 := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [traceFrom, List.length_cons, inductionHypothesis,
        List.length_cons]
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace

end
