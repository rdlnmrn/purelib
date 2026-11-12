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

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian

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
  Basic.CanonicalCoefficients.CoefficientPolynomial) :
    List Basic.CanonicalCoefficients.CoefficientPolynomial → List
      Basic.CanonicalCoefficients.CoefficientPolynomial
  | [] => [-previous]
  | current :: remaining =>
      (Multiplication.Coordinate.SeparatedVariables.twiceShift current - previous) ::
        SeparatedVariables.reflectedTailStep current
          remaining

/-- One Horner step for substitution by `2T-U`, in low-to-high `U`
coefficients.

An empty table starts from the conjugated constant coefficient. A nonempty
table updates its head and retains the same reflected tail recursion. -/
@[expose] def SeparatedVariables.reflectedStep (coefficients : List
  Basic.CanonicalCoefficients.CoefficientPolynomial)
    (coefficient : Basic.Canonical) : List (Basic.DensePolynomial Basic.Canonical) :=
  match coefficients with
  | [] => [Coefficients.Constants.SeparatedVariables.parameterConstant (Basic.Canonical.conj
    coefficient)]
  | head :: tail =>
      (Multiplication.Coordinate.SeparatedVariables.twiceShift head -
        Coefficients.Constants.SeparatedVariables.parameterConstant (-Basic.Canonical.conj
        coefficient)) ::
        SeparatedVariables.reflectedTailStep head tail

section
/-- The ascending reflected-tail step evaluates to the reflected affine multiplier times the old tail, minus its
preceding coefficient.

The preceding polynomial and the ascending tail are evaluated at the same
parameter. Their scalar values retain the displayed affine multiplier. -/
private theorem evalLow_reflectedTailStep (previous :
  Basic.CanonicalCoefficients.CoefficientPolynomial)
    (coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial) (outer parameter :
      Basic.Canonical) :
    Ascending.evalLow
      (SeparatedVariables.reflectedTailStep previous coefficients) outer
      parameter =
      (2 * parameter - outer) * Ascending.evalLow coefficients outer parameter -
        previous.eval parameter := by
  induction coefficients generalizing previous with
  | nil =>
      rw [SeparatedVariables.reflectedTailStep,
        Ascending.evalLow_cons]
      rw [Basic.DensePolynomial.eval_neg]
      change -previous.eval parameter + outer * 0 =
        (2 * parameter - outer) * 0 - previous.eval parameter
      rw [mul_zero, add_zero, mul_zero, zero_sub]
  | cons coefficient remaining inductionHypothesis =>
      rw [SeparatedVariables.reflectedTailStep,
        Ascending.evalLow_cons, Basic.DensePolynomial.eval_sub,
        Multiplication.Coordinate.eval_twiceShift,
        inductionHypothesis, Ascending.evalLow_cons]
      exact Algebra.Ring.Affine.reflectedTailRingIdentity 2 parameter
        (coefficient.eval parameter) (previous.eval parameter) outer
        (Ascending.evalLow remaining outer parameter)
end

/-- A reflected coefficient step evaluates as a Horner step at twice the parameter minus the outer variable.

The coefficient table is evaluated at the retained parameter and outer
argument. Its next scalar step uses the same conjugated coefficient. -/
theorem evalLow_reflectedStep (coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial)
    (coefficient outer parameter : Basic.Canonical) :
    Ascending.evalLow
      (SeparatedVariables.reflectedStep coefficients coefficient) outer
      parameter =
      Ascending.evalLow coefficients outer parameter * (2 * parameter - outer) +
        Basic.Canonical.conj coefficient := by
  cases coefficients with
  | nil =>
      rw [SeparatedVariables.reflectedStep,
        Ascending.evalLow_cons, Coefficients.Constants.eval_parameterConstant]
      change Basic.Canonical.conj coefficient + outer * 0 =
        0 * (2 * parameter - outer) + Basic.Canonical.conj coefficient
      rw [mul_zero, add_zero, zero_mul, zero_add]
  | cons head tail =>
      rw [SeparatedVariables.reflectedStep,
        Ascending.evalLow_cons, Basic.DensePolynomial.eval_sub,
        Multiplication.Coordinate.eval_twiceShift,
        Coefficients.Constants.eval_parameterConstant,
          evalLow_reflectedTailStep,
          Ascending.evalLow_cons]
      exact Algebra.Ring.Affine.reflectedStepRingIdentity 2 parameter
        (head.eval parameter)
        (Basic.Canonical.conj coefficient) outer (Ascending.evalLow tail outer
          parameter)

section
/-- The complete reflected coefficient fold evaluates as the conjugated scalar Horner fold at the reflected argument.

The supplied state equality initializes the two folds at the same scalar
value. Each retained coefficient applies the corresponding reflected step. -/
private theorem evalLow_foldl_reflectedStep (outer parameter : Basic.Canonical) :
    ∀ (coefficients : List Basic.Canonical)
      (state : List Basic.CanonicalCoefficients.CoefficientPolynomial) (value : Basic.Canonical),
      Ascending.evalLow state outer parameter = value →
      Ascending.evalLow (coefficients.foldl
        SeparatedVariables.reflectedStep state) outer parameter =
        coefficients.foldl
          (fun accumulator coefficient =>
            accumulator * (2 * parameter - outer) + Basic.Canonical.conj coefficient)
          value
  | [], _, _, stateEvaluation => stateEvaluation
  | coefficient :: remaining, state, value, stateEvaluation => by
      simp only [List.foldl_cons]
      apply Basic.evalLow_foldl_reflectedStep
        outer parameter remaining
      rw [evalLow_reflectedStep, stateEvaluation]
end

/-- Double the retained parameter-leading coefficient at each reflected Horner step. -/
@[expose] def reflectedLeadingStep (leading : Basic.Canonical) (_ : Basic.Canonical) :
  Basic.Canonical :=
  2 * leading

/-- Compute ascending outer coefficients of the coefficient-conjugated polynomial at 2T−U.

The normalized source table is folded from its conjugated leading constant; an empty source retains an empty table. -/
@[expose] def SeparatedVariables.reflectedCoefficients (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
  :
    List (Basic.DensePolynomial Basic.Canonical) :=
  match p.normalize.coeffs with
  | [] => []
  | leading :: remaining =>
      remaining.foldl SeparatedVariables.reflectedStep
        [Coefficients.Constants.SeparatedVariables.parameterConstant (Basic.Canonical.conj
        leading)]

/-- Compute the parameter-leading coefficient by doubling the conjugated source leader through the remaining coefficient
list.

The leading coefficient is conjugated once; the remaining normalized
coefficients determine the number of retained doubling steps. -/
@[expose] def reflectedLeading (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Basic.Canonical :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl reflectedLeadingStep (Basic.Canonical.conj
        leading)

/-- The polynomial `conj(p)(2T-U)`.

Reversing the computed ascending outer table places the same coefficients
in the dense bivariate representation. -/
@[expose] def SeparatedVariables.reflected (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  (Basic.DenseBivariate Basic.Canonical) :=
  ⟨(SeparatedVariables.reflectedCoefficients p).reverse⟩

/-- The reflected bivariate polynomial evaluates to the conjugate of the original value at the conjugated reflected
argument.

The normalized coefficient fold retains the same conjugated coefficients.
The scalar argument is the conjugate of twice the parameter minus the
outer coordinate. -/
@[simp] theorem eval_reflected (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (outer parameter : Basic.Canonical) :
    Basic.eval (SeparatedVariables.reflected p) outer
      parameter =
      Basic.Canonical.conj (p.eval (Basic.Canonical.conj (2 * parameter - outer))) := by
  rw [← Basic.DensePolynomial.eval_normalize p (Basic.Canonical.conj (2 * parameter - outer))]
  change Ascending.evalLow
    (SeparatedVariables.reflectedCoefficients p) outer parameter =
    Basic.Canonical.conj (p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * Basic.Canonical.conj (2 * parameter - outer) + coefficient) 0)
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have reflectedEmpty : SeparatedVariables.reflectedCoefficients p = [] :=
        by
        rw [SeparatedVariables.reflectedCoefficients, coefficients]
      rw [reflectedEmpty]
      rfl
  | cons leading remaining =>
      have initialEvaluation :
          Ascending.evalLow
            [Coefficients.Constants.SeparatedVariables.parameterConstant (Basic.Canonical.conj
            leading)] outer parameter =
            Basic.Canonical.conj leading := by
        rw [Ascending.evalLow_cons,
          Coefficients.Constants.eval_parameterConstant]
        change Basic.Canonical.conj leading + outer * 0 =
          Basic.Canonical.conj leading
        rw [mul_zero, add_zero]
      have reflectedFold := evalLow_foldl_reflectedStep
        outer parameter
        remaining [Coefficients.Constants.SeparatedVariables.parameterConstant
          (Basic.Canonical.conj leading)] (Basic.Canonical.conj leading)
        initialEvaluation
      have conjugatedFold := Conjugate.Evaluation.conj_evalFold (2 * parameter -
        outer)
        remaining leading
      rw [SeparatedVariables.reflectedCoefficients, coefficients]
      simp only [List.foldl_cons]
      rw [show (0 : Basic.Canonical) * Basic.Canonical.conj (2 * parameter - outer) + leading =
          leading by ring1]
      exact reflectedFold.trans conjugatedFold.symm

end Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic

end
