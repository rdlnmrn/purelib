module
import Purelib.Algebra.NatCast
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Natural.Inverse
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Evaluation
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

namespace Purelib.Polynomial.Ascending.Gaussian.Dense.Antiderivative

open Purelib.Algebra in
/-- Weighted Horner identity for the integrated coefficient tail.  The
weight accounts for its offset from the constant term.

The original degree-indexed coefficient divisions are canceled by their positive natural denominators, and the unchanged
finite Horner tail supplies its value and derivative readings. -/
private theorem integrated_jet (coefficients : List
  Gaussian.Basic.Canonical) (degree : Nat) (point : Gaussian.Basic.Canonical) :
    ((degree + 1 : Nat) : Gaussian.Basic.Canonical) * (Ascending.Gaussian.Dense.Evaluation.jet
      (Ascending.Gaussian.Antiderivative.antiderivativeCoefficients degree coefficients) point).1 +
      point * (Ascending.Gaussian.Dense.Evaluation.jet
        (Ascending.Gaussian.Antiderivative.antiderivativeCoefficients degree coefficients) point).2 =
        Ascending.Gaussian.Evaluation.evalCoeffs coefficients point := open Purelib.Algebra.Field in by
  induction coefficients generalizing degree with
  | nil =>
      simp only [Ascending.Gaussian.Antiderivative.antiderivativeCoefficients,
        Ascending.Gaussian.Dense.Evaluation.jet_nil, Ascending.Gaussian.Evaluation.evalCoeffs, List.foldr_nil,
        Gaussian.Basic.mul_zero, _root_.add_zero, -eq_self, -iff_self]
      rfl
  | cons coefficient remaining inductionHypothesis =>
      have divided : ((degree + 1 : Nat) : Gaussian.Basic.Canonical) *
          (coefficient / ((degree + 1 : Nat) : Gaussian.Basic.Canonical)) = coefficient := by
        rw [ExplicitField.div_eq_mul_inv, Gaussian.Field.inv_eq]
        calc
          _ = coefficient * (((degree + 1 : Nat) : Gaussian.Basic.Canonical) * Gaussian.Field.inv ((degree + 1
            : Nat) : Gaussian.Basic.Canonical)) := by
            ring1
          _ = coefficient := by
            rw [Gaussian.Field.mul_inv _ (Gaussian.Natural.Inverse.nat_succ_nonzero degree), _root_.mul_one]
      have shifted : ((degree + 1 + 1 : Nat) : Gaussian.Basic.Canonical) = ((degree + 1 : Nat) :
        Gaussian.Basic.Canonical) + 1 := by
        rw [NatCast.add, Nat.cast_one]
      simp only [Ascending.Gaussian.Antiderivative.antiderivativeCoefficients,
        Ascending.Gaussian.Dense.Evaluation.jet_cons, Ascending.Gaussian.Evaluation.evalCoeffs, List.foldr_cons]
      calc
        _ = ((degree + 1 : Nat) : Gaussian.Basic.Canonical) * (coefficient / ((degree + 1 : Nat) :
          Gaussian.Basic.Canonical)) +
            point * ((((degree + 1 : Nat) : Gaussian.Basic.Canonical) + 1) *
              (Ascending.Gaussian.Dense.Evaluation.jet
                (Ascending.Gaussian.Antiderivative.antiderivativeCoefficients (degree + 1) remaining) point).1 +
              point * (Ascending.Gaussian.Dense.Evaluation.jet
                (Ascending.Gaussian.Antiderivative.antiderivativeCoefficients (degree + 1) remaining) point).2) := by
                ring1
        _ = coefficient + point * Ascending.Gaussian.Evaluation.evalCoeffs remaining point := by
          rw [divided, <- shifted, inductionHypothesis]
        _ = _ := rfl

/-- The dense derivative of the converted Gaussian antiderivative evaluates to the original polynomial.

The value-and-derivative Horner recurrence cancels the positive-degree coefficient divisions directly. -/
theorem toDense_antiderivative_derivative (polynomial
  : Polynomial.Ascending.Gaussian.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.GCD.derivative (Ascending.Gaussian.Dense.Evaluation.toDense
      (Ascending.Gaussian.Antiderivative.antiderivative polynomial))).eval point =
      Ascending.Gaussian.Evaluation.eval polynomial point := by
  rw [Ascending.Gaussian.Dense.Evaluation.toDense_derivative_eval]
  change (Ascending.Gaussian.Dense.Evaluation.jet (0 ::
    Ascending.Gaussian.Antiderivative.antiderivativeCoefficients 0 polynomial.coefficients) point).2 = _
  rw [Ascending.Gaussian.Dense.Evaluation.jet_cons]
  have identity := integrated_jet polynomial.coefficients 0 point
  simpa only [Nat.zero_add, Nat.cast_one, _root_.one_mul, _root_.mul_comm, _root_.add_comm,
    Ascending.Gaussian.Evaluation.eval] using identity

end Purelib.Polynomial.Ascending.Gaussian.Dense.Antiderivative

end
