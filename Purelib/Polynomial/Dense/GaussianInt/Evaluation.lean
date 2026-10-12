module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Arithmetic.Scale
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.GaussianInt.Evaluation

/-- Horner evaluation after embedding a Gaussian-integer coefficient list. -/
def evalIntegers (point : Gaussian.Basic.Canonical) (coefficients
  : List GaussianInt) : Gaussian.Basic.Canonical :=
  Dense.Basic.DensePolynomial.evalCoeffs point (coefficients.map
    GaussianInt.toGaussian)

/-- An empty Gaussian-integer coefficient list evaluates to zero. -/
@[simp] theorem evalIntegers_nil (point :
  Gaussian.Basic.Canonical) :
    evalIntegers point [] = 0 := rfl

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Data Purelib.Data.List

/-- Evaluating a nonempty integer coefficient list separates its leading term.

The remaining list retains its original length and coefficient occurrences;
coordinate embedding changes neither the power exponent nor the tail reading. -/
theorem evalIntegers_cons (point : Gaussian.Basic.Canonical)
  (coefficient : GaussianInt)
    (remaining : List GaussianInt) :
    evalIntegers point (coefficient :: remaining) =
      GaussianInt.toGaussian coefficient *
          point ^ remaining.length +
        evalIntegers point remaining := by
  change DensePolynomial.evalCoeffs point
    (GaussianInt.toGaussian coefficient :: remaining.map GaussianInt.toGaussian) = _
  rw [DensePolynomial.evalCoeffs_cons_expansion, Map.length_map]
  rfl

/-- Scaling every integer coefficient scales its Gaussian evaluation.

The displayed natural factor multiplies the original evaluation without
changing coefficient order, list length or the evaluation point. -/
theorem evalIntegers_map_scale (point : Gaussian.Basic.Canonical)
  (factor : Nat)
    (coefficients : List GaussianInt) :
    evalIntegers point (coefficients.map (Data.GaussianInt.Arithmetic.Scale.scale
      factor)) =
      ⟨(factor : Fraction.Rational), 0⟩ * evalIntegers point coefficients := by
  induction coefficients with
  | nil =>
      exact (Gaussian.Basic.mul_zero _).symm
  | cons coefficient remaining inductionHypothesis =>
      rw [List.map_cons, evalIntegers_cons,
        evalIntegers_cons, Map.length_map,
        Data.GaussianInt.Arithmetic.Scale.toGaussian_scale, inductionHypothesis]
      ring1
end Purelib.Polynomial.Dense.GaussianInt.Evaluation

end
