module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Quadratic.TracePair.Basic
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Reverse
import Purelib.Data.Bool.Decide
public import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.Quadratic (TracePair)

open Purelib

open Purelib.Polynomial

section
public section

/-!
# Integer-table evaluation in a quadratic trace basis

A finite ascending integer coefficient table evaluates to its scalar and
generator coordinates in the retained quadratic trace pair. The list
recursion uses the relation `alpha² = trace * alpha - 1`. Addition, scaling,
negation, convolution and removal of leading zero slots preserve that exact
formal evaluation.
-/

namespace Purelib.Algebra.Quadratic.TracePair

variable {K : Type*} [ExplicitField K]

/-- Evaluate an ascending integer polynomial at the formal quadratic
generator, retaining its two trace coordinates. -/
@[expose] def eval : List Int → K → TracePair K
  | [], _ => zero
  | coefficient :: remaining, trace =>
      let recursive := eval remaining trace
      ⟨(coefficient : K) - recursive.generator,
        recursive.scalar + trace * recursive.generator⟩

/-- The empty integer table evaluates to the zero quadratic trace pair. -/
@[simp] theorem eval_nil (trace : K) : eval [] trace = zero := rfl

/-- Evaluate a nonempty integer table using the quadratic generator relation.

The new scalar coordinate is the cast head minus the tail generator coordinate; the new generator coordinate is the tail
scalar plus trace times its generator. -/
@[simp] theorem eval_cons (coefficient : Int) (remaining : List Int)
    (trace : K) :
    eval (coefficient :: remaining) trace =
      ⟨(coefficient : K) - (eval remaining trace).generator,
        (eval remaining trace).scalar +
          trace * (eval remaining trace).generator⟩ := rfl

/-- Formal quadratic evaluation preserves padded addition of integer coefficient tables. -/
theorem eval_add (left right : List Int) (trace : K) :
    eval (Ascending.Integer.Basic.Certificate.add left right) trace =
      add (eval left trace) (eval right trace) := by
  induction left generalizing right with
  | nil =>
      apply ext <;> simp only [Ascending.Integer.Basic.Certificate.add, eval, zero, add, -eq_self, -iff_self] <;> ring0
  | cons coefficient remaining inductionHypothesis =>
      cases right with
      | nil =>
          apply ext <;> simp only [Ascending.Integer.Basic.Certificate.add, eval,
            zero, add, -eq_self, -iff_self] <;> ring0
      | cons other others =>
          rw [Ascending.Integer.Basic.Certificate.add, eval_cons,
            eval_cons, eval_cons, inductionHypothesis others]
          apply ext <;> simp only [add, Algebra.Ring.IntCast.add] <;> ring0

/-- Formal quadratic evaluation sends integer coefficient scaling to trace-pair scaling by the cast factor. -/
theorem eval_scale (factor : Int) (coefficients : List Int) (trace : K) :
    eval (Ascending.Integer.Basic.Certificate.scale factor coefficients) trace =
      scale (factor : K) (eval coefficients trace) := open Purelib.Algebra in by
  induction coefficients with
  | nil =>
      apply ext <;> simp only [Ascending.Integer.Basic.Certificate.scale,
        eval, zero, scale, -eq_self, -iff_self] <;> ring0
  | cons coefficient remaining inductionHypothesis =>
      rw [Ascending.Integer.Basic.Certificate.scale, eval_cons, eval_cons,
        inductionHypothesis]
      apply ext <;>
        simp only [scale, Ring.IntCast.intCast_mul] <;> ring0

/-- Negating an integer coefficient table negates its formal quadratic value. -/
theorem eval_neg (coefficients : List Int) (trace : K) :
    eval (Ascending.Integer.Basic.neg coefficients) trace =
      neg (eval coefficients trace) := by
  rw [Ascending.Integer.Basic.neg, eval_scale]
  apply ext <;> simp only [scale, neg] <;> ring0

/-- Formal quadratic evaluation preserves coefficient subtraction. -/
theorem eval_sub (left right : List Int) (trace : K) :
    eval (Ascending.Integer.Basic.sub left right) trace =
      sub (eval left trace) (eval right trace) := by
  rw [Ascending.Integer.Basic.sub, eval_add, eval_neg]
  apply ext <;> simp only [add, neg, sub] <;> ring0

/-- Shifting an integer table multiplies its formal quadratic value by the generator. -/
theorem eval_shift (coefficients : List Int) (trace : K) :
    eval (Ascending.Integer.Basic.shift coefficients) trace =
      mul trace alpha (eval coefficients trace) := by
  rw [Ascending.Integer.Basic.shift, eval_cons,
    alpha_mul]
  apply ext <;> simp only [Algebra.Ring.IntCast.cast_zero, -eq_self, -iff_self] <;> ring0

/-- Formal quadratic evaluation turns integer coefficient convolution into trace-pair multiplication.

The scalar and generator coordinates satisfy the same finite Horner recurrence under `a² = t*a - 1`. -/
theorem eval_mul (left right : List Int) (trace : K) :
    eval (Ascending.Integer.Basic.Certificate.mul left right) trace =
      mul trace (eval left trace) (eval right trace) := by
  induction left with
  | nil =>
      rw [Ascending.Integer.Basic.Certificate.mul, eval_nil, mul_zero_left]
  | cons coefficient remaining inductionHypothesis =>
      rw [Ascending.Integer.Basic.Certificate.mul, eval_add, eval_scale]
      change add
          (scale (coefficient : K) (eval right trace))
          (eval (Ascending.Integer.Basic.shift
            (Ascending.Integer.Basic.Certificate.mul remaining right)) trace) = _
      rw [eval_shift, inductionHypothesis, eval_cons]
      apply ext <;> simp only [add, scale, mul, alpha] <;> ring0

/-- Appending a zero in a new highest-degree slot does not change evaluation
at the formal quadratic generator. -/
theorem eval_append_zero : ∀ coefficients : List Int, ∀ trace : K,
    eval (coefficients ++ [0]) trace = eval coefficients trace
  | [], trace => by
      change eval [0] trace = eval [] trace
      apply ext <;> simp only [eval, zero, Algebra.Ring.IntCast.cast_zero, -eq_self, -iff_self] <;> ring0
  | coefficient :: remaining, trace => by
      rw [List.cons_append, eval_cons, eval_cons,
        eval_append_zero remaining trace]

/-- Removing leading zeroes from a descending coefficient list does not
change evaluation after it is returned to ascending order. -/
theorem eval_reverse_dropWhile_zero : ∀ values : List Int, ∀ trace : K,
    eval ((values.dropWhile fun value => value = 0).reverse) trace =
      eval values.reverse trace
  | [], trace => rfl
  | value :: remaining, trace => by
      by_cases valueZero : value = 0
      · subst value
        rw [Data.List.DropWhile.cons_of_true (fun value : Int => decide (value = 0)) 0 remaining (by decide),
          Data.List.Reverse.reverse_cons,
          eval_append_zero, eval_reverse_dropWhile_zero remaining
            trace]
      · have rejected : decide (value = 0) = false :=
          Data.Bool.Decide.bool_eq_false_of_not_eq_true _
            (fun selected => valueZero (of_decide_eq_true selected))
        rw [Data.List.DropWhile.cons_of_false (fun value : Int => decide (value = 0)) value remaining rejected]
end Purelib.Algebra.Quadratic.TracePair

end
