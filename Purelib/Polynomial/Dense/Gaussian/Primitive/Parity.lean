module

import Purelib.Algebra.NatCast
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Data.List.Fold
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

/-!
# Finite primitives after identity or square substitution

For e=1 or e=2, integrate C(t^e) as t G(t^e). A single coefficient pass
divides the coefficient of w^n by en+1. The value and derivative identities
are finite Horner proofs over constructive Gaussian rationals.
-/

@[expose] public section

-- Retain exact public scalar/carrier shorthand names after subject placement.

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Parity

open Purelib.Algebra
open Purelib.Data.List

/-- The canonical Gaussian rational coefficient type. -/
abbrev CanonicalScalar := Gaussian.Basic.Canonical
/-- Dense polynomials over canonical Gaussian rationals. -/
abbrev CoefficientPolynomial := Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Data.Gaussian.Basic.Canonical

/-- Select exponent two for ramified substitution and exponent one otherwise. -/
def degree (ramified : Bool) : Nat := if ramified then 2 else 1

/-- Construct a dense polynomial from coefficients in ascending degree order. -/
private def fromLow (coefficients : List CanonicalScalar) : CoefficientPolynomial := ⟨coefficients.reverse⟩

/-- Evaluate an ascending coefficient table together with its formal derivative.

The right fold retains the value and derivative at the same Gaussian point. -/
private def jet (coefficients : List CanonicalScalar) (point :
  CanonicalScalar) : CanonicalScalar × CanonicalScalar :=
  coefficients.foldr (fun coefficient state =>
    (state.1 * point + coefficient, state.2 * point + state.1)) (0, 0)

/-- The empty ascending table has zero value and derivative. -/
private theorem jet_nil (point : CanonicalScalar) : jet []
  point = (0, 0) := rfl

/-- Prepending a constant coefficient gives the ascending Horner jet step. -/
private theorem jet_cons (coefficient : CanonicalScalar) (remaining : List
  CanonicalScalar) (point : CanonicalScalar) :
    jet (coefficient :: remaining) point =
      ((jet remaining point).1 * point + coefficient,
        (jet remaining point).2 * point + (jet remaining
        point).1) := rfl

/-- The ascending jet value equals evaluation of the reversed dense table.

Reversing the coefficient list turns the retained ascending Horner recursion
into the dense evaluation fold at the same Gaussian point. -/
private theorem eval_fromLow (coefficients : List CanonicalScalar) (point :
  CanonicalScalar) :
    (fromLow coefficients).eval point = (jet
      coefficients point).1 := open Purelib in by
  unfold fromLow DensePolynomial.eval DensePolynomial.evalCoeffs
  rw [Data.List.Fold.foldl_reverse]
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining previous =>
      rw [List.foldr_cons, jet_cons, previous]

/-- The ascending jet derivative equals evaluation of the formal derivative. -/
private theorem derivative_fromLow (coefficients : List CanonicalScalar) (point :
  CanonicalScalar) :
    (Dense.Derivative.derivative (fromLow coefficients)).eval point =
      (jet coefficients point).2 := open Purelib in by
  rw [Dense.Derivative.eval_derivative]
  unfold Dense.Derivative.evalDerivativeCoeffs fromLow
  rw [Data.List.Fold.foldl_reverse]
  rfl

/-- Divide each ascending coefficient by its primitive weight.

At offset k the divisor is exponent * k + 1; recursive entries increment the offset. -/
def weighted (exponent : Nat) : Nat → List CanonicalScalar → List
  CanonicalScalar
  | _, [] => []
  | offset, coefficient :: remaining => coefficient / ((exponent * offset + 1 : Nat) :
    CanonicalScalar) ::
      weighted exponent (offset + 1) remaining

/-- Every primitive weight exponent * offset + 1 is nonzero as a Gaussian scalar. -/
private theorem weight_nonzero (exponent offset : Nat) : ((exponent * offset + 1 : Nat) :
  CanonicalScalar) ≠ 0 := open Purelib.Data.Rat in by
  intro zero
  have real := congrArg (fun value : CanonicalScalar => value.re) zero
  rw [Gaussian.Cast.natCast_re, Gaussian.Basic.zero_re] at real
  exact (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ (exponent * offset))).ne' real

/-- The weighted table satisfies its value-and-derivative reconstruction identity.

Multiplying its value by the initial weight and its derivative by exponent times the point recovers the original
ascending evaluation. -/
private theorem weighted_jet (exponent offset : Nat) (coefficients : List CanonicalScalar)
  (point : CanonicalScalar) :
    ((exponent * offset + 1 : Nat) : CanonicalScalar) * (jet
      (weighted exponent offset coefficients) point).1 +
      (exponent : CanonicalScalar) * point * (jet
        (weighted exponent offset coefficients) point).2 =
        (jet coefficients point).1 := open Purelib.Algebra.Field in by
  induction coefficients generalizing offset with
  | nil =>
      change ((exponent * offset + 1 : Nat) : CanonicalScalar) * 0 + (exponent : CanonicalScalar) * point * 0 = 0
      rw [Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero]
  | cons coefficient remaining previous =>
      have paid : ((exponent * offset + 1 : Nat) : CanonicalScalar) *
          (coefficient / ((exponent * offset + 1 : Nat) : CanonicalScalar)) = coefficient := by
        rw [Gaussian.Basic.mul_comm]
        exact ExplicitField.div_mul_cancel _ (weight_nonzero exponent offset)
      have next : ((exponent * (offset + 1) + 1 : Nat) : CanonicalScalar) =
          ((exponent * offset + 1 : Nat) : CanonicalScalar) + (exponent :
            CanonicalScalar) := by
        rw [show exponent * (offset + 1) + 1 = exponent * offset + 1 + exponent by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_right_comm],
          NatCast.add]
      simp only [weighted, jet_cons]
      calc
        _ = ((exponent * offset + 1 : Nat) : CanonicalScalar) * (coefficient / ((exponent *
          offset + 1 : Nat) : CanonicalScalar)) +
            point * ((((exponent * offset + 1 : Nat) : CanonicalScalar) + (exponent :
              CanonicalScalar)) *
              (jet (weighted exponent (offset + 1)
                remaining) point).1 +
                (exponent : CanonicalScalar) * point * (jet
                  (weighted exponent (offset + 1) remaining) point).2) := by ring1
        _ = coefficient + point * (jet remaining point).1 := by
          rw [paid, ← next, previous]
        _ = _ := by ring1

/-- Insert a zero after each ascending coefficient to substitute the square variable. -/
def spread : List CanonicalScalar → List CanonicalScalar
  | [] => []
  | coefficient :: remaining => coefficient :: 0 :: spread remaining

/-- Spreading coefficients evaluates at the square and scales the derivative by twice the point.

The inserted zero coefficients preserve each original entry and replace its
monomial by the corresponding even power; both jet components follow the same recursion. -/
private theorem jet_spread (coefficients : List CanonicalScalar) (point :
  CanonicalScalar) :
    jet (spread coefficients) point =
      ((jet coefficients (point ^ 2)).1,
      2 * point * (jet coefficients (point ^ 2)).2) := by
  induction coefficients with
  | nil =>
      change ((0 : CanonicalScalar), 0) = (0, 2 * point * 0)
      rw [Gaussian.Basic.mul_zero]
  | cons coefficient remaining previous =>
      simp only [spread, jet_cons, previous]
      apply Prod.ext <;> dsimp only <;> ring1

/-- Dense coefficients of t G(t^e), retaining the finite substitution
structure so operational evaluators can transport the same polynomial. -/
def valueCoefficients (factor : CoefficientPolynomial) (ramified : Bool) : List CanonicalScalar :=
  (0 :: (if ramified then spread factor.coeffs.reverse else
    factor.coeffs.reverse)).reverse

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CanonicalScalar -> Gaussian in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CoefficientPolynomial -> Dense in
set_option genInjectivity false in
/-- A retained primitive and its factor for linear or squared substitution.

The value is t times the factor at t to the selected exponent, with exact coefficient and derivative certificates for
the original polynomial. -/
structure Data (polynomial : CoefficientPolynomial) (ramified : Bool) where
  /-- The retained weighted factor polynomial. -/ factor : CoefficientPolynomial
  /-- The retained primitive polynomial. -/ value : CoefficientPolynomial
  /-- Evaluation factors as the argument times the factor at the selected power. -/ value_eq : ∀ point, value.eval point
    = point * factor.eval (point ^ degree ramified)
  /-- The primitive derivative evaluates to the original polynomial at the selected power. -/ derivative_eq : ∀ point,
    (Dense.Derivative.derivative value).eval point =
    polynomial.eval (point ^ degree ramified)
  /-- The primitive retains the exact coefficient table computed from the factor. -/ value_coeffs : value.coeffs =
    valueCoefficients factor ramified
  /-- The factor and its scaled derivative reconstruct the original polynomial. -/ factor_derivative : ∀ point,
    factor.eval point + (degree ramified : CanonicalScalar) * point *
    (Dense.Derivative.derivative factor).eval point = polynomial.eval point

constructive_injectivity Data

namespace Data.mk

end Data.mk

namespace Data.mk

end Data.mk

section
open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CanonicalScalar -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CoefficientPolynomial -> Dense
/-- The finite coefficient pass certifies the displayed value and derivative identities.

The original reversed table, weighted factor and substituted value polynomial
are retained together. Their four certificates express evaluation, formal
derivative, exact coefficient selection and factor reconstruction. -/
theorem build_certificates (polynomial : CoefficientPolynomial) (ramified : Bool) :
    let coefficients := polynomial.coeffs.reverse
    let weights := weighted (degree ramified) 0 coefficients
    let factor : Dense := ⟨weights.reverse⟩
    let expanded := if ramified then spread weights else weights
    let value : Dense := ⟨(0 :: expanded).reverse⟩
    (∀ point, value.eval point = point * factor.eval (point ^ degree ramified)) ∧
      (∀ point, (Dense.Derivative.derivative value).eval point =
        polynomial.eval (point ^ degree ramified)) ∧
      value.coeffs = valueCoefficients factor ramified ∧
      (∀ point, factor.eval point + (degree ramified : CanonicalScalar) * point *
        (Dense.Derivative.derivative factor).eval point =
          polynomial.eval point) := by
  let coefficients := polynomial.coeffs.reverse
  let weights := weighted (degree ramified) 0 coefficients
  let factor : Dense := ⟨weights.reverse⟩
  let expanded := if ramified then spread weights else weights
  let value : Dense := ⟨(0 :: expanded).reverse⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro point
    change (fromLow (0 :: expanded)).eval point =
      point * (fromLow weights).eval (point ^ degree ramified)
    rw [eval_fromLow, jet_cons,
      eval_fromLow]
    cases ramified
    · change (jet weights point).1 * point + 0 = point *
        (jet weights (point ^ 1)).1
      rw [pow_one]
      ring1
    · change (jet (spread weights) point).1 * point + 0
        = point * (jet weights (point ^ 2)).1
      rw [jet_spread]
      ring1
  · intro point
    change (Dense.Derivative.derivative
      (fromLow (0 :: expanded))).eval point =
        polynomial.eval (point ^ degree ramified)
    rw [derivative_fromLow, jet_cons]
    have original (value : CanonicalScalar) : (jet coefficients
      value).1 = polynomial.eval value := by
      rw [← eval_fromLow]
      change (DensePolynomial.mk polynomial.coeffs.reverse.reverse).eval value = _
      rw [Reverse.reverse_reverse]
    have identity : (jet weights (point ^ degree ramified)).1 +
        (degree ramified : CanonicalScalar) * point ^ degree ramified *
          (jet weights (point ^ degree ramified)).2 =
          (jet coefficients (point ^ degree ramified)).1 := by
      have paid := weighted_jet (degree ramified) 0 coefficients (point ^ degree
        ramified)
      rw [Nat.mul_zero, Nat.zero_add, Nat.cast_one, Gaussian.Basic.one_mul] at paid
      exact paid
    cases ramified
    ·
      change (jet weights point).2 * point + (jet
        weights point).1 = polynomial.eval (point ^ 1)
      rw [pow_one, ← original]
      have normalized : (jet weights point).1 + point *
        (jet weights point).2 =
          (jet coefficients point).1 := by
        change (jet weights (point ^ 1)).1 +
          (1 : Gaussian) * point ^ 1 * (jet weights (point ^ 1)).2 =
            (jet coefficients (point ^ 1)).1 at identity
        rw [pow_one, Gaussian.Basic.one_mul] at identity
        exact identity
      calc
        _ = (jet weights point).1 + point * (jet weights
          point).2 := by
          ring1
        _ = _ := normalized
    ·
      change (jet (spread weights) point).2 * point +
        (jet (spread weights) point).1 = polynomial.eval
        (point ^ 2)
      rw [jet_spread, ← original]
      have combined : 2 * point * (jet weights (point ^ 2)).2 * point +
        (jet weights (point ^ 2)).1 =
          (jet weights (point ^ 2)).1 + 2 * point ^ 2 *
            (jet weights (point ^ 2)).2 := by ring1
      rw [combined]
      change (jet weights (point ^ 2)).1 +
        (2 : Gaussian) * point ^ 2 * (jet weights (point ^ 2)).2 =
          (jet coefficients (point ^ 2)).1 at identity
      exact identity
  · change (0 :: expanded).reverse =
      (0 :: (if ramified then spread weights.reverse.reverse else
        weights.reverse.reverse)).reverse
    rw [Reverse.reverse_reverse]
  · intro point
    change (fromLow weights).eval point + (degree ramified :
      CanonicalScalar) * point *
      (Dense.Derivative.derivative (fromLow weights)).eval point =
        polynomial.eval point
    rw [eval_fromLow, derivative_fromLow]
    have identity := weighted_jet (degree ramified) 0 coefficients point
    have original : (jet coefficients point).1 = polynomial.eval point := by
      rw [← eval_fromLow]
      change (DensePolynomial.mk polynomial.coeffs.reverse.reverse).eval point = _
      rw [Reverse.reverse_reverse]
    rw [original] at identity
    rw [Nat.mul_zero, Nat.zero_add, Nat.cast_one, Gaussian.Basic.one_mul] at identity
    exact identity

namespace Data

/-- Build the executable primitive and retain its finite certificates. -/
def build (polynomial : CoefficientPolynomial) (ramified : Bool) :
  Data polynomial ramified := by
  let coefficients := polynomial.coeffs.reverse
  let weights := weighted (degree ramified) 0 coefficients
  let factor : Dense := ⟨weights.reverse⟩
  let expanded := if ramified then spread weights else weights
  let value : Dense := ⟨(0 :: expanded).reverse⟩
  obtain ⟨valueEq, derivativeEq, coeffEq, factorEq⟩ :=
    build_certificates polynomial ramified
  exact ⟨factor, value, valueEq, derivativeEq, coeffEq, factorEq⟩

end Data

end

namespace Data

/-- The retained primitive vanishes at the origin. -/
theorem value_zero {polynomial : CoefficientPolynomial} {ramified : Bool} (data :
  Data polynomial ramified) : data.value.eval 0 = 0 := by
  rw [data.value_eq, Gaussian.Basic.zero_mul]

end Data

end Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
