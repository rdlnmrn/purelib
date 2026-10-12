module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.EventAlgebra.Basic
public import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Simple observables on explicit finite event algebras

A simple observable is a displayed finite linear combination of indicators
of coded events.  Its value and integral are exact rational computations.
The truth-signature representation proves that the same finite algebra atoms
which determine event measure also determine every such integral.
-/

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain an event code from the exact algebra together with its rational coefficient. -/
structure SimpleTerm {α : Type} (algebra : EventAlgebra α) where
  /-- The exact code in the retained event algebra. -/ event : algebra.Code
  /-- The rational coefficient multiplying this event's indicator. -/ coefficient : Fraction.Rational

constructive_injectivity SimpleTerm

section
open Purelib.Data.Rat

end

/-- Represent a simple observable by its exact finite ordered list of algebra-coded rational terms. -/
abbrev SimpleObservable {α : Type} (algebra : EventAlgebra α) :=
  List (SimpleTerm algebra)

namespace SimpleObservable

section
open Purelib.Data.Rat
/-- Sum each retained term's event indicator times its coefficient at the supplied payload. -/
def evaluate {α : Type} {algebra : EventAlgebra α} :
    SimpleObservable algebra → α → Fraction.Rational
  | [], _ => 0
  | term :: remaining, item =>
      Distribution.indicator (algebra.evaluate term.event) item *
          term.coefficient +
        evaluate remaining item

/-- Sum retained term coefficients against their exact algebra-code lookups in the supplied Boolean signature. -/
def signatureValue {α : Type} {algebra : EventAlgebra α} :
    SimpleObservable algebra → List Bool → Fraction.Rational
  | [], _ => 0
  | term :: remaining, signature =>
      Distribution.indicator (algebra.signatureEvent term.event) signature *
          term.coefficient +
        signatureValue remaining signature

end

/-- Evaluating the exact payload signature gives the original simple observable's value. -/
theorem signatureValue_signature {α : Type}
    {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra) (item : α) :
    observable.signatureValue (algebra.signature item) =
      observable.evaluate item := by
  induction observable with
  | nil => rfl
  | cons term remaining inductionHypothesis =>
      simp only [signatureValue, evaluate, inductionHypothesis, -eq_self, -iff_self]
      have indicatorSame :
          Distribution.indicator (algebra.signatureEvent term.event)
              (algebra.signature item) =
            Distribution.indicator (algebra.evaluate term.event) item := by
        unfold Distribution.indicator
        rw [algebra.signatureEvent_signature term.event item]
      rw [indicatorSame]

/-- Payloads with equal signatures have equal values for every retained simple observable over that algebra. -/
theorem evaluate_eq_of_signature_eq {α : Type}
    {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra) {left right : α}
    (same : algebra.signature left = algebra.signature right) :
    observable.evaluate left = observable.evaluate right := by
  rw [← observable.signatureValue_signature left,
    ← observable.signatureValue_signature right, same]

/-- Concatenate two exact simple-term lists over the same retained event algebra. -/
def add {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra) : SimpleObservable algebra :=
  left ++ right

/-- Evaluating concatenated simple terms adds their two original values. -/
theorem evaluate_add {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra) (item : α) :
    (left.add right).evaluate item =
      left.evaluate item + right.evaluate item := by
  unfold add
  induction left with
  | nil =>
      simp only [List.nil_append, evaluate, zero_add, -eq_self, -iff_self]
      rfl
  | cons term remaining inductionHypothesis =>
      simp only [List.cons_append, evaluate, -eq_self, -iff_self]
      rw [inductionHypothesis]
      ring1

section
open Purelib.Data.Rat
/-- Multiply every retained term coefficient by the supplied factor, preserving exact event codes and order. -/
def scale {α : Type} {algebra : EventAlgebra α}
    (factor : Fraction.Rational) (observable : SimpleObservable algebra) :
    SimpleObservable algebra :=
  observable.map fun term =>
    { event := term.event
      coefficient := factor * term.coefficient }

/-- Scaling all retained coefficients scales the simple observable's value by the same factor. -/
theorem evaluate_scale {α : Type} {algebra : EventAlgebra α}
    (factor : Fraction.Rational) (observable : SimpleObservable algebra)
    (item : α) :
    (observable.scale factor).evaluate item =
      factor * observable.evaluate item := by
  induction observable with
  | nil =>
      simp only [scale, List.map_nil, evaluate, mul_zero, -eq_self, -iff_self]
      rfl
  | cons term remaining inductionHypothesis =>
      unfold scale at inductionHypothesis
      simp only [scale, List.map_cons, evaluate, -eq_self, -iff_self]
      rw [inductionHypothesis]
      ring1

end

/-- Negate the simple observable by scaling its exact coefficients by minus one. -/
def neg {α : Type} {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra) : SimpleObservable algebra :=
  observable.scale (-1)

/-- Negating the retained simple terms negates their evaluated value. -/
theorem evaluate_neg {α : Type} {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra) (item : α) :
    observable.neg.evaluate item = -observable.evaluate item := by
  unfold neg
  rw [observable.evaluate_scale]
  ring1

/-- Append the negated right term list to the exact left simple observable. -/
def sub {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra) : SimpleObservable algebra :=
  left.add right.neg

/-- Evaluating the retained difference of simple observables subtracts their original values. -/
theorem evaluate_sub {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra) (item : α) :
    (left.sub right).evaluate item =
      left.evaluate item - right.evaluate item := by
  unfold sub
  rw [left.evaluate_add, right.evaluate_neg]
  ring1

/-- Multiply one exact term through the right list using algebra-code intersections and coefficient products. -/
private def mulTerm {α : Type} {algebra : EventAlgebra α}
    (left : SimpleTerm algebra) (right : SimpleObservable algebra) :
    SimpleObservable algebra :=
  right.map fun term =>
    { event := algebra.intersection left.event term.event
      coefficient := left.coefficient * term.coefficient }

/-- The distributed term list evaluates to the original term value times the right observable's value. -/
private theorem evaluate_mulTerm {α : Type}
    {algebra : EventAlgebra α} (left : SimpleTerm algebra) :
    ∀ (right : SimpleObservable algebra) (item : α),
      (mulTerm left right).evaluate item =
        (Distribution.indicator (algebra.evaluate left.event) item *
          left.coefficient) * right.evaluate item
  | [], item => by
      simp only [mulTerm, List.map_nil, evaluate, mul_zero, -eq_self, -iff_self]
      rfl
  | term :: remaining, item => by
      simp only [mulTerm, List.map_cons, evaluate, -eq_self, -iff_self]
      unfold mulTerm at evaluate_mulTerm
      rw [evaluate_mulTerm left remaining item]
      unfold Distribution.indicator
      rw [algebra.evaluate_intersection]
      cases algebra.evaluate left.event item <;>
        cases algebra.evaluate term.event item <;>
        simp only [Bool.false_and, Bool.true_and, -eq_self, -iff_self] <;>
        ring1

/-- Form the ordered finite product expansion using exact code intersections and coefficient products.

Enumerate every right term for each left term in original list order, retaining all positional products even when codes
repeat. -/
def mul {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra) : SimpleObservable algebra :=
  left.flatMap fun term =>
    right.map fun next =>
      { event := algebra.intersection term.event next.event
        coefficient := term.coefficient * next.coefficient }

/-- The exact finite product expansion evaluates to the product of the original simple observable values. -/
theorem evaluate_mul {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra) (item : α) :
    (left.mul right).evaluate item =
      left.evaluate item * right.evaluate item := by
  induction left with
  | nil =>
      simp only [mul, -eq_self, -iff_self]
      change (0 : _) = 0 * right.evaluate item
      exact (zero_mul _).symm
  | cons term remaining inductionHypothesis =>
      have termEvaluation :
          ∀ (rows : SimpleObservable algebra) (point : α),
            SimpleObservable.evaluate
              (rows.map fun next : SimpleTerm algebra =>
                SimpleTerm.mk (algebra.intersection term.event next.event)
                  (term.coefficient * next.coefficient)) point =
              (Distribution.indicator (algebra.evaluate term.event) point *
                term.coefficient) * rows.evaluate point := by
        intro rows point
        induction rows with
        | nil =>
            simp only [List.map_nil, evaluate, mul_zero, -eq_self, -iff_self]
            rfl
        | cons next rest inductionHypothesis =>
            simp only [List.map_cons, evaluate, -eq_self, -iff_self]
            rw [inductionHypothesis]
            unfold Distribution.indicator
            rw [algebra.evaluate_intersection]
            cases algebra.evaluate term.event point <;>
              cases algebra.evaluate next.event point <;>
              simp only [Bool.false_and, Bool.true_and, -eq_self, -iff_self] <;>
              ring1
      change evaluate
        ((right.map fun next =>
          { event := algebra.intersection term.event next.event
            coefficient := term.coefficient * next.coefficient }) ++
          mul remaining right) item = _
      have appendEvaluation :=
        evaluate_add
          (right.map fun next =>
            { event := algebra.intersection term.event next.event
              coefficient := term.coefficient * next.coefficient })
          (mul remaining right) item
      unfold add at appendEvaluation
      rw [appendEvaluation, termEvaluation, inductionHypothesis]
      simp only [evaluate, -eq_self, -iff_self]
      ring1
end SimpleObservable

end Purelib.Measure

end
