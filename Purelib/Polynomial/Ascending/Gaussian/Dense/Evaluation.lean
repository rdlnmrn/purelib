module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Fold
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite antiderivatives of dense Gaussian polynomials

Connect the existing low-to-high polynomial integrator to the dense
high-to-low polynomial algebra.  The derivative identity is proved by finite
Horner induction.  The existing finite Taylor estimate then bounds local
primitive increments, without analytic limits or infinite series.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation

/-- Convert an ascending Gaussian coefficient table to the descending dense representation by reversal. -/
def toDense (polynomial :
  CoefficientPolynomial) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  ⟨polynomial.coefficients.reverse⟩

/-- Reversing the coefficient representation preserves the Gaussian polynomial value. -/
theorem toDense_eval (polynomial :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (Ascending.Gaussian.Dense.Evaluation.toDense polynomial).eval point = Ascending.Gaussian.Evaluation.eval polynomial
      point := open Purelib in by
  unfold Ascending.Gaussian.Dense.Evaluation.toDense Dense.Basic.DensePolynomial.eval
    Dense.Basic.DensePolynomial.evalCoeffs
  rw [Data.List.Fold.foldl_reverse]
  unfold Ascending.Gaussian.Evaluation.eval Ascending.Gaussian.Evaluation.evalCoeffs
  induction polynomial.coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.foldr_cons, inductionHypothesis]
      ring1

/-- Compute the value and derivative of an ascending Gaussian table in one finite Horner fold.

The first state component is the value and the second is the derivative value at the same supplied point. -/
public def jet (coefficients : List
  Gaussian.Basic.Canonical) (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical :=
  coefficients.foldr (fun coefficient state =>
    (state.1 * point + coefficient, state.2 * point + state.1)) (0, 0)

/-- The empty table has value-and-derivative state `(0, 0)`. -/
public theorem jet_nil (point : Gaussian.Basic.Canonical)
  : Ascending.Gaussian.Dense.Evaluation.jet [] point = (0, 0) := rfl

/-- Extend the Gaussian Horner state by one coefficient.

The value becomes the tail value times the point plus the coefficient; the derivative becomes the tail derivative times
the point plus the tail value. -/
public theorem jet_cons (coefficient :
  Gaussian.Basic.Canonical) (remaining : List Gaussian.Basic.Canonical) (point : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Dense.Evaluation.jet (coefficient :: remaining) point =
      ((Ascending.Gaussian.Dense.Evaluation.jet remaining point).1 * point + coefficient,
        (Ascending.Gaussian.Dense.Evaluation.jet remaining point).2 * point + (Ascending.Gaussian.Dense.Evaluation.jet
          remaining point).1) := rfl

/-- The derivative value in the descending dense representation is the second component of the ascending Horner state.
-/
public theorem toDense_derivative_eval (polynomial :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.GCD.derivative (Ascending.Gaussian.Dense.Evaluation.toDense polynomial)).eval point =
      (Ascending.Gaussian.Dense.Evaluation.jet polynomial.coefficients point).2 := open Purelib in by
  unfold Dense.Gaussian.GCD.derivative
  rw [Dense.Derivative.eval_derivative]
  unfold Dense.Derivative.evalDerivativeCoeffs Ascending.Gaussian.Dense.Evaluation.toDense
  rw [Data.List.Fold.foldl_reverse]
  rfl

end Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation

end
