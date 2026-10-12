module
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Polynomial.Ascending.Integer.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# The finite Goh--Wildberger spread-cyclotomic factorization

This file completes Exercise 8.13 without roots, completed fields, or an
infinite polynomial family.  Ordinary cyclotomic factors are constructed by
finite monic long division over the constructive rationals.  Their integer
coefficients are reduced through the formal quadratic relation
`a^2 = t*a - 1`, and the resulting norm is evaluated at `t = 2 - 4s`.

The sole exceptional norm is `Phi_1`, whose norm is `4s`; this supplies the
one global factor `4` in the spread--Lucas identity.  Cancellation is done
only over the constructive rationals, after which the resulting integer
coefficient identity is transported to every explicitly supplied field,
including finite characteristic.
-/

namespace Purelib.Polynomial.Ascending.Integer.Evaluation

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

section
/-- Appending one high-degree coefficient adds its cast value times the argument raised to the preceding list length. -/
private theorem
  eval_append_singleton
    (coefficients : List Int) (coefficient : Int) (value : K) :
    Ascending.Integer.Basic.eval (coefficients ++ [coefficient]) value =
      Ascending.Integer.Basic.eval coefficients value + (coefficient : K) * value ^ coefficients.length := by
  induction coefficients with
  | nil =>
      simp only [List.nil_append, Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, mul_zero,
        add_zero,
        List.length_nil, pow_zero, mul_one, zero_add, -eq_self, -iff_self] ; rfl
  | cons head remaining inductionHypothesis =>
      rw [List.cons_append, Ascending.Integer.Basic.eval_cons, inductionHypothesis, Ascending.Integer.Basic.eval_cons,
        List.length_cons, pow_succ]
      ring0
/-- A coefficient list tabulated on a finite range evaluates to its finite power sum.

The summand at each index is the cast integer coefficient times the evaluation argument raised to that index. -/
public theorem
  eval_map_range
  : ∀ (count : Nat) (coefficient : Nat → Int)
    (value : K),
    Ascending.Integer.Basic.eval ((List.range count).map coefficient) value =
      FiniteSum.Prefix.prefixSum count fun index =>
        (coefficient index : K) * value ^ index
  | 0, coefficient, value => rfl
  | count + 1, coefficient, value => by
      rw [Data.List.Range.Basic.range_succ, Data.List.Map.map_append, List.map_singleton,

          Purelib.Polynomial.Ascending.Integer.Evaluation.eval_append_singleton,
          Data.List.Map.length_map, Data.List.Range.Basic.length_range,
        FiniteSum.Prefix.prefixSum_succ_last,

          Purelib.Polynomial.Ascending.Integer.Evaluation.eval_map_range
          count coefficient value]
end

end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Ascending.Integer.Evaluation

end
