module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
public import Purelib.Polynomial.Ascending.Integer.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Ascending coefficients of unit monomials and power differences

The original integer coefficient recursion shifts a retained unit table once
per degree. Subtraction retains the original constant-one table, and direct
scalar evaluation identifies the two coefficient programs in any explicit field.
-/

namespace Purelib.Polynomial.Ascending.Integer.PowerMinusOne.IntegerPolynomial

open Purelib.Algebra.Field
open Purelib.Polynomial.Ascending.Integer
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- Ascending coefficients of `X^degree`.

Every successor degree prepends the original integer zero through the retained
shift operation. The same unit entry and table tail determine all coefficients. -/
@[expose] public def monomialCoefficients : Nat → List Int
  | 0 => [1]
  | degree + 1 => Basic.shift (monomialCoefficients degree)

/-- Ascending coefficients of `X^degree-1`.

The original padded integer subtraction uses the displayed unit monomial and
the same singleton constant-one table, preserving both original coefficient inputs. -/
@[expose] public def powerMinusOneCoefficients (degree : Nat) : List Int :=
  Basic.sub (monomialCoefficients degree) [1]

/-- The recursively shifted unit monomial evaluates to the corresponding argument power.

The retained unit table evaluates to one at degree zero. Each original shift
adds exactly one factor of the supplied point in the same explicit field. -/
@[simp] public theorem eval_monomialCoefficients
    {K : Type*} [ExplicitField K] : ∀ degree : Nat, ∀ point : K,
    Basic.eval (monomialCoefficients degree) point = point ^ degree
  | 0, point => by
      change ((1 : Int) : K) + point * 0 = point ^ 0
      rewrite [Int.cast_one, mul_zero, add_zero, pow_zero]
      exact Eq.refl _
  | degree + 1, point => by
      rw [monomialCoefficients, Basic.eval_shift,
        eval_monomialCoefficients degree point, pow_succ]
      ring0

/-- The power-minus-one coefficient table evaluates to the corresponding argument power minus one.

The original integer subtraction transports its two retained evaluations.
The singleton unit table evaluates directly to the same field unit. -/
@[simp] public theorem eval_powerMinusOneCoefficients
    {K : Type*} [ExplicitField K] (degree : Nat) (point : K) :
    Basic.eval (powerMinusOneCoefficients degree) point = point ^ degree - 1 := by
  rw [powerMinusOneCoefficients, Basic.eval_sub, eval_monomialCoefficients]
  rewrite [Basic.eval_cons, Basic.eval_nil,
    Int.cast_one, mul_zero, add_zero]
  exact Eq.refl _
end Purelib.Polynomial.Ascending.Integer.PowerMinusOne.IntegerPolynomial
