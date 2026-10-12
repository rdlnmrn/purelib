module

import Purelib.Algebra.Ring.Affine
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Conjugate.Evaluation
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Bivariate.Basic
public import Purelib.Polynomial.Dense.Bivariate.Gaussian.Ascending
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
public import Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

/-!
# Reflected Gaussian bivariate coefficient tables

Finite reflected Horner steps retain the normalized coefficient table and
its ascending outer order. Scalar readback laws evaluate that same table at
the reflected argument and its retained parameter.
-/

public section

namespace Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic

open Purelib.Data
open Purelib.Polynomial

/-- Remaining low coefficients after the new constant coefficient.

An empty tail contributes the negative preceding coefficient. Each
retained head is multiplied by twice the parameter before subtracting its
preceding coefficient. -/
@[expose] def SeparatedVariables.reflectedTailStep (previous :
  Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial → List
      Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  | [] => [-previous]
  | current :: remaining =>
      (Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift current - previous) ::
        Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep current
          remaining

/-- One Horner step for substitution by `2T-U`, in low-to-high `U`
coefficients.

An empty table starts from the conjugated constant coefficient. A nonempty
table updates its head and retains the same reflected tail recursion. -/
@[expose] def SeparatedVariables.reflectedStep (coefficients : List
  Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (coefficient : Gaussian.Basic.Canonical) : List (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  match coefficients with
  | [] => [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant (Gaussian.Basic.Canonical.conj
    coefficient)]
  | head :: tail =>
      (Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift head -
        Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant (-Gaussian.Basic.Canonical.conj
        coefficient)) ::
        Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep head tail

section
/-- The ascending reflected-tail step evaluates to the reflected affine multiplier times the old tail, minus its
preceding coefficient.

The preceding polynomial and the ascending tail are evaluated at the same
parameter. Their scalar values retain the displayed affine multiplier. -/
private theorem evalLow_reflectedTailStep (previous :
  Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (coefficients : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (outer parameter :
      Gaussian.Basic.Canonical) :
    Dense.Bivariate.Gaussian.Ascending.evalLow
      (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep previous coefficients) outer
      parameter =
      (2 * parameter - outer) * Dense.Bivariate.Gaussian.Ascending.evalLow coefficients outer parameter -
        previous.eval parameter := by
  induction coefficients generalizing previous with
  | nil =>
      rw [Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep,
        Dense.Bivariate.Gaussian.Ascending.evalLow_cons]
      rw [Dense.Basic.DensePolynomial.eval_neg]
      change -previous.eval parameter + outer * 0 =
        (2 * parameter - outer) * 0 - previous.eval parameter
      rw [mul_zero, add_zero, mul_zero, zero_sub]
  | cons coefficient remaining inductionHypothesis =>
      rw [Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep,
        Dense.Bivariate.Gaussian.Ascending.evalLow_cons, Dense.Basic.DensePolynomial.eval_sub,
        Dense.Gaussian.Multiplication.Coordinate.eval_twiceShift,
        inductionHypothesis, Dense.Bivariate.Gaussian.Ascending.evalLow_cons]
      exact Purelib.Algebra.Ring.Affine.reflectedTailRingIdentity 2 parameter
        (coefficient.eval parameter) (previous.eval parameter) outer
        (Dense.Bivariate.Gaussian.Ascending.evalLow remaining outer parameter)
end

/-- A reflected coefficient step evaluates as a Horner step at twice the parameter minus the outer variable.

The coefficient table is evaluated at the retained parameter and outer
argument. Its next scalar step uses the same conjugated coefficient. -/
theorem evalLow_reflectedStep (coefficients : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (coefficient outer parameter : Gaussian.Basic.Canonical) :
    Dense.Bivariate.Gaussian.Ascending.evalLow
      (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep coefficients coefficient) outer
      parameter =
      Dense.Bivariate.Gaussian.Ascending.evalLow coefficients outer parameter * (2 * parameter - outer) +
        Gaussian.Basic.Canonical.conj coefficient := by
  cases coefficients with
  | nil =>
      rw [Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep,
        Dense.Bivariate.Gaussian.Ascending.evalLow_cons, Dense.Gaussian.Coefficients.Constants.eval_parameterConstant]
      change Gaussian.Basic.Canonical.conj coefficient + outer * 0 =
        0 * (2 * parameter - outer) + Gaussian.Basic.Canonical.conj coefficient
      rw [mul_zero, add_zero, zero_mul, zero_add]
  | cons head tail =>
      rw [Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep,
        Dense.Bivariate.Gaussian.Ascending.evalLow_cons, Dense.Basic.DensePolynomial.eval_sub,
        Dense.Gaussian.Multiplication.Coordinate.eval_twiceShift,
        Dense.Gaussian.Coefficients.Constants.eval_parameterConstant,
          Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic.evalLow_reflectedTailStep,
          Dense.Bivariate.Gaussian.Ascending.evalLow_cons]
      exact Purelib.Algebra.Ring.Affine.reflectedStepRingIdentity 2 parameter
        (head.eval parameter)
        (Gaussian.Basic.Canonical.conj coefficient) outer (Dense.Bivariate.Gaussian.Ascending.evalLow tail outer
          parameter)

section
/-- The complete reflected coefficient fold evaluates as the conjugated scalar Horner fold at the reflected argument.

The supplied state equality initializes the two folds at the same scalar
value. Each retained coefficient applies the corresponding reflected step. -/
private theorem evalLow_foldl_reflectedStep (outer parameter : Gaussian.Basic.Canonical) :
    ∀ (coefficients : List Gaussian.Basic.Canonical)
      (state : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (value : Gaussian.Basic.Canonical),
      Dense.Bivariate.Gaussian.Ascending.evalLow state outer parameter = value →
      Dense.Bivariate.Gaussian.Ascending.evalLow (coefficients.foldl
        Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep state) outer parameter =
        coefficients.foldl
          (fun accumulator coefficient =>
            accumulator * (2 * parameter - outer) + Gaussian.Basic.Canonical.conj coefficient)
          value
  | [], _, _, stateEvaluation => stateEvaluation
  | coefficient :: remaining, state, value, stateEvaluation => by
      simp only [List.foldl_cons]
      apply Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic.evalLow_foldl_reflectedStep
        outer parameter remaining
      rw [Dense.Bivariate.Gaussian.Reflection.Basic.evalLow_reflectedStep, stateEvaluation]
end

/-- Double the retained parameter-leading coefficient at each reflected Horner step. -/
@[expose] def reflectedLeadingStep (leading : Gaussian.Basic.Canonical) (_ : Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  2 * leading

/-- Compute ascending outer coefficients of the coefficient-conjugated polynomial at 2T−U.

The normalized source table is folded from its conjugated leading constant; an empty source retains an empty table. -/
@[expose] def SeparatedVariables.reflectedCoefficients (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  :
    List (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  match p.normalize.coeffs with
  | [] => []
  | leading :: remaining =>
      remaining.foldl Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep
        [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant (Gaussian.Basic.Canonical.conj
        leading)]

/-- Compute the parameter-leading coefficient by doubling the conjugated source leader through the remaining coefficient
list.

The leading coefficient is conjugated once; the remaining normalized
coefficients determine the number of retained doubling steps. -/
@[expose] def reflectedLeading (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Gaussian.Basic.Canonical :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl Dense.Bivariate.Gaussian.Reflection.Basic.reflectedLeadingStep (Gaussian.Basic.Canonical.conj
        leading)

/-- The polynomial `conj(p)(2T-U)`.

Reversing the computed ascending outer table places the same coefficients
in the dense bivariate representation. -/
@[expose] def SeparatedVariables.reflected (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  (Dense.Bivariate.Basic.DenseBivariate Gaussian.Basic.Canonical) :=
  ⟨(Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p).reverse⟩

/-- The reflected bivariate polynomial evaluates to the conjugate of the original value at the conjugated reflected
argument.

The normalized coefficient fold retains the same conjugated coefficients.
The scalar argument is the conjugate of twice the parameter minus the
outer coordinate. -/
@[simp] theorem eval_reflected (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (outer parameter : Gaussian.Basic.Canonical) :
    Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
      parameter =
      Gaussian.Basic.Canonical.conj (p.eval (Gaussian.Basic.Canonical.conj (2 * parameter - outer))) := by
  rw [← Dense.Basic.DensePolynomial.eval_normalize p (Gaussian.Basic.Canonical.conj (2 * parameter - outer))]
  change Dense.Bivariate.Gaussian.Ascending.evalLow
    (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p) outer parameter =
    Gaussian.Basic.Canonical.conj (p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * Gaussian.Basic.Canonical.conj (2 * parameter - outer) + coefficient) 0)
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have reflectedEmpty : Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p = [] :=
        by
        rw [Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients, coefficients]
      rw [reflectedEmpty]
      rfl
  | cons leading remaining =>
      have initialEvaluation :
          Dense.Bivariate.Gaussian.Ascending.evalLow
            [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant (Gaussian.Basic.Canonical.conj
            leading)] outer parameter =
            Gaussian.Basic.Canonical.conj leading := by
        rw [Dense.Bivariate.Gaussian.Ascending.evalLow_cons,
          Dense.Gaussian.Coefficients.Constants.eval_parameterConstant]
        change Gaussian.Basic.Canonical.conj leading + outer * 0 =
          Gaussian.Basic.Canonical.conj leading
        rw [mul_zero, add_zero]
      have reflectedFold := Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic.evalLow_foldl_reflectedStep
        outer parameter
        remaining [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant
          (Gaussian.Basic.Canonical.conj leading)] (Gaussian.Basic.Canonical.conj leading)
        initialEvaluation
      have conjugatedFold := Purelib.Data.Gaussian.Conjugate.Evaluation.conj_evalFold (2 * parameter -
        outer)
        remaining leading
      rw [Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients, coefficients]
      simp only [List.foldl_cons]
      rw [show (0 : Gaussian.Basic.Canonical) * Gaussian.Basic.Canonical.conj (2 * parameter - outer) + leading =
          leading by ring1]
      exact reflectedFold.trans conjugatedFold.symm

end Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic

end
