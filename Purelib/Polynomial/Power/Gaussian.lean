module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Fold
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Nat.Subtraction
public import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Gaussian.Derivative.Monomial
import Purelib.Polynomial.Dense.Gaussian.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients

/-!
# Gaussian power polynomials

The original finite descending coefficient program constructs Z^degree-input
from its supplied positive degree. Evaluation, normalization and derivative
certificates retain those same coefficients and the original coordinate-power program.
-/

namespace Purelib.Polynomial.Power.Gaussian

open Purelib.Data
open Purelib.Polynomial

/-- Construct the descending coefficient table for Z^degree-input.

The original leading one is followed by degree-1 zero coefficients and the
negated input constant, retaining the supplied positive degree. -/
@[expose] public def rootPolynomial (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  ⟨1 :: (List.replicate (degree.value - 1) 0 ++ [-input])⟩

/-- Changing the constant parameter leaves the original formal derivative unchanged.

The final derivative-state step ignores its constant coefficient. Both
parameter tables therefore retain exactly the same derivative coefficient list. -/
public theorem derivative_polynomial_eq (source target : Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) :
    Gaussian.GCD.derivative (rootPolynomial source degree) =
      Gaussian.GCD.derivative (rootPolynomial target degree) := by
  apply Basic.DensePolynomial.ext
  unfold Gaussian.GCD.derivative Derivative.derivative
    Derivative.derivativeState rootPolynomial
  change ((List.replicate (degree.value - 1) (0 : Gaussian.Basic.Canonical) ++ [-source]).foldl
      Derivative.derivativeStep (Derivative.derivativeStep (0, 0) 1)).2.coeffs =
    ((List.replicate (degree.value - 1) (0 : Gaussian.Basic.Canonical) ++ [-target]).foldl
      Derivative.derivativeStep (Derivative.derivativeStep (0, 0) 1)).2.coeffs
  let initial : CoefficientPolynomial ×
    CoefficientPolynomial :=
    Derivative.derivativeStep (0, 0) 1
  have sourceReadback := List.Fold.foldl_append Derivative.derivativeStep
    (List.replicate (degree.value - 1) (0 : Gaussian.Basic.Canonical)) [-source] initial
  have targetReadback := List.Fold.foldl_append Derivative.derivativeStep
    (List.replicate (degree.value - 1) (0 : Gaussian.Basic.Canonical)) [-target] initial
  exact (congrArg (fun state : CoefficientPolynomial ×
    CoefficientPolynomial => state.2.coeffs) sourceReadback).trans
    (congrArg (fun state : CoefficientPolynomial ×
      CoefficientPolynomial => state.2.coeffs) targetReadback).symm

/-- The root coefficient table evaluates to the specified positive power minus its input.

The original Horner scan retains the leading one, the degree-1 zero block
and the final negated input coefficient. -/
public theorem rootPolynomial_eval (input point : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (rootPolynomial input degree).eval point =
      point ^ degree.value - input := by
  have predecessor : degree.value - 1 + 1 = degree.value := by
    exact (Nat.add_comm _ _).trans (Nat.Subtraction.add_sub_of_le degree.positive)
  change
    Basic.DensePolynomial.evalCoeffs point
        (1 :: (List.replicate (degree.value - 1) 0 ++ [-input])) =
      point ^ degree.value - input
  rw [show
      1 :: (List.replicate (degree.value - 1) 0 ++ [-input]) =
        ([1] ++ List.replicate (degree.value - 1) 0) ++ [-input] by rfl]
  rw [Gaussian.Evaluation.evalCoeffs_append_singleton,
    Basic.DensePolynomial.evalCoeffs_append_replicate_zero]
  change ((0 * point + 1) * point ^ (degree.value - 1)) * point + -input =
    point ^ degree.value - input
  rewrite [Gaussian.Basic.zero_mul,
    Gaussian.Basic.zero_add,
    Gaussian.Basic.one_mul, ← pow_succ, predecessor]
  exact Gaussian.Basic.sub_eq_add_neg _ _

/-- The monic root coefficient table is already normalized.

Its original leading coefficient is one. The retained zero-prefix test therefore
keeps the entire original coefficient spine. -/
public theorem rootPolynomial_normalized (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (rootPolynomial input degree).normalize = rootPolynomial input degree := by
  apply Basic.DensePolynomial.ext
  change ((1 : Gaussian.Basic.Canonical) ::
    (List.replicate (degree.value - 1) 0 ++ [-input])).dropWhile
      (fun value => decide (value = 0)) =
    1 :: (List.replicate (degree.value - 1) 0 ++ [-input])
  exact List.DropWhile.cons_of_false
    (fun value : Gaussian.Basic.Canonical => decide (value = 0))
    1 (List.replicate (degree.value - 1) 0 ++ [-input]) (by decide)

/-- The positive coordinate-power program minus the parameter constant equals the retained power polynomial.

Both original normalized coefficient programs have the same evaluations at
the existing finite comparison candidates, giving structural polynomial equality. -/
public theorem polynomial_eq_coordinatePower_sub_constant
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    rootPolynomial parameter degree =
      Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1) -
        Basic.DensePolynomial.constant parameter := by
  apply Extensionality.normalized_eq_of_sub_isZero
    (rootPolynomial_normalized parameter degree)
    (Basic.DensePolynomial.normalize_sub _ _)
  apply Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro point _member
  rw [Basic.DensePolynomial.eval_sub, rootPolynomial_eval,
    Gaussian.Power.Coordinate.coordinatePositivePower_eval, Basic.DensePolynomial.eval_constant]
  rewrite [(Nat.add_comm _ _).trans (Nat.Subtraction.add_sub_of_le degree.positive)]
  exact Eq.refl _

/-- The derivative of Z^degree-parameter evaluates to degree times Z^(degree-1).

The retained coordinate-power program gives the variable term; the original
constant parameter has zero formal derivative. -/
public theorem derivative_eval (parameter point : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Gaussian.GCD.derivative
      (rootPolynomial parameter degree)).eval point =
      (degree.value : Gaussian.Basic.Canonical) * point ^ (degree.value - 1) := by
  unfold Gaussian.GCD.derivative
  rw [polynomial_eq_coordinatePower_sub_constant,
    Derivative.eval_derivative_sub,
    Gaussian.Derivative.Monomial.derivative_coordinatePositivePower_eval]
  have derivativeConstant :
      (Derivative.derivative
        (Basic.DensePolynomial.constant parameter)).eval point = 0 := by
    rw [Derivative.eval_derivative]
    change
      (Derivative.evalDerivativeCoeffs point [parameter]).2 = 0
    change (0 : Gaussian.Basic.Canonical) * point + 0 = 0
    rewrite [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add]
    exact Eq.refl _
  rewrite [derivativeConstant, Gaussian.Basic.sub_zero,
    (Nat.add_comm _ _).trans (Nat.Subtraction.add_sub_of_le degree.positive)]
  exact Eq.refl _

/-- The root polynomial has the exact retained positive degree.

Its original leading-one table is normalized and has one leading entry,
degree-1 zeros and the original final constant entry. -/
public theorem rootPolynomial_degree (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (rootPolynomial input degree).natDegree = degree.value := by
  change
    (rootPolynomial input degree).normalize.coeffs.length - 1 = degree.value
  rw [rootPolynomial_normalized]
  change (List.replicate (degree.value - 1) (0 : Gaussian.Basic.Canonical) ++ [-input]).length + 1 - 1 =
    degree.value
  rewrite [List.Append.length_append, List.Replicate.length_replicate]
  change (degree.value - 1 + 1) + 1 - 1 = degree.value
  rewrite [Nat.Subtraction.add_sub_cancel_right]
  exact (Nat.add_comm _ _).trans (Nat.Subtraction.add_sub_of_le degree.positive)

end Purelib.Polynomial.Power.Gaussian
