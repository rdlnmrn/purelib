module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Ascending.Integer.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Basic

open Purelib.Algebra.Field

open Purelib.Polynomial

/-!
# Finite integer-polynomial certificates

Integer coefficient lists are stored in ascending degree order.  The
primitive-recursive operations below let a literal finite Bezout identity be
checked by kernel reduction over `Int`, then evaluated in any constructive
explicit field.  This is useful for prime-field exclusions without listing
or searching an ambient carrier.
-/

public section

namespace Purelib.Polynomial.Ascending.Integer.Composition

/-- A finite natural power in the coefficient-list ring. -/
@[expose] def power (coefficients : List Int) : Nat → List Int
  | 0 => [1]
  | exponent + 1 => Ascending.Integer.Basic.Certificate.mul (power
    coefficients exponent) coefficients

/-- The zeroth finite polynomial power is the singleton one table. -/
@[simp] theorem power_zero (coefficients : List Int) :
    power coefficients 0 = [1] := rfl

/-- The next finite polynomial power multiplies the preceding table by the original table. -/
@[simp] theorem power_succ (coefficients : List Int) (exponent :
  Nat) :
    power coefficients (exponent + 1) =
      Ascending.Integer.Basic.Certificate.mul (power coefficients exponent) coefficients
        := rfl

/-- Evaluation preserves natural powers of integer coefficient tables.

Each recursive coefficient-table multiplication evaluates as scalar multiplication over the supplied explicit field. -/
theorem eval_power {K : Type*} [ExplicitField K]
    (coefficients : List Int) (exponent : Nat) (value : K) :
    Ascending.Integer.Basic.eval (power coefficients exponent) value =
      Ascending.Integer.Basic.eval coefficients value ^ exponent := by
  induction exponent with
  | zero =>
      simp only [power_zero, Ascending.Integer.Basic.eval_cons,
        Ascending.Integer.Basic.eval_nil, Int.cast_one, mul_zero,
        add_zero, pow_zero, -eq_self, -iff_self]
      rfl
  | succ exponent inductionHypothesis =>
      rw [power_succ, Ascending.Integer.Basic.eval_mul, inductionHypothesis, pow_succ]

/-- Substitute one finite integer polynomial into another by Horner
recursion. -/
@[expose] def compose : List Int → List Int → List Int
  | [], _ => []
  | coefficient :: remaining, inner =>
      Ascending.Integer.Basic.Certificate.add [coefficient] (Ascending.Integer.Basic.Certificate.mul inner
        (compose remaining inner))

/-- Substituting into the empty outer coefficient table returns the empty table. -/
@[simp] theorem compose_nil (inner : List Int) :
  compose [] inner = [] := rfl

/-- Horner substitution adds the outer head to the inner polynomial times the substituted tail. -/
@[simp] theorem compose_cons (coefficient : Int) (remaining
  inner : List Int) :
    compose (coefficient :: remaining) inner =
      Ascending.Integer.Basic.Certificate.add [coefficient] (Ascending.Integer.Basic.Certificate.mul inner
        (compose remaining inner)) := rfl

/-- Evaluation of a substituted integer polynomial equals successive evaluation of the inner and outer tables.

Horner substitution retains the original coefficient order and evaluates the inner table at the supplied scalar before
evaluating the outer table. -/
theorem eval_compose {K : Type*} [ExplicitField K]
    (outer inner : List Int) (value : K) :
    Ascending.Integer.Basic.eval (compose outer inner) value =
      Ascending.Integer.Basic.eval outer (Ascending.Integer.Basic.eval inner value) := by
  induction outer with
  | nil =>
      simp only [compose_nil, Ascending.Integer.Basic.eval_nil, -eq_self, -iff_self]
      rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [compose_cons, Ascending.Integer.Basic.eval_add,
        Ascending.Integer.Basic.eval_mul, inductionHypothesis]
      simp only [Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, mul_zero, add_zero, -eq_self,
        -iff_self]
      rfl
end Purelib.Polynomial.Ascending.Integer.Composition

end
