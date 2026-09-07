import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EventAlgebra

/-!
# Simple observables on explicit finite event algebras

A simple observable is a displayed finite linear combination of indicators
of coded events.  Its value and integral are exact rational computations.
The truth-signature representation proves that the same finite algebra atoms
which determine event measure also determine every such integral.
-/

namespace FiniteMeasure

/-- One coefficient times the indicator of one coded algebra event. -/
structure SimpleTerm {α : Type} (algebra : FiniteEventAlgebra α) where
  event : algebra.Code
  coefficient : Coordinate

/-- A displayed finite linear combination of coded event indicators. -/
abbrev SimpleObservable {α : Type} (algebra : FiniteEventAlgebra α) :=
  List (SimpleTerm algebra)

namespace SimpleObservable

/-- Exact rational value of a simple observable at one payload. -/
def evaluate {α : Type} {algebra : FiniteEventAlgebra α} :
    SimpleObservable algebra → α → Coordinate
  | [], _ => 0
  | term :: remaining, item =>
      Distribution.indicator (algebra.evaluate term.event) item *
          term.coefficient +
        evaluate remaining item

/-- Evaluate the same simple observable directly on a finite algebra truth
signature. -/
def signatureValue {α : Type} {algebra : FiniteEventAlgebra α} :
    SimpleObservable algebra → List Bool → Coordinate
  | [], _ => 0
  | term :: remaining, signature =>
      Distribution.indicator (algebra.signatureEvent term.event) signature *
          term.coefficient +
        signatureValue remaining signature

theorem signatureValue_signature {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra) (item : α) :
    observable.signatureValue (algebra.signature item) =
      observable.evaluate item := by
  induction observable with
  | nil => rfl
  | cons term remaining inductionHypothesis =>
      simp only [signatureValue, evaluate, inductionHypothesis]
      have indicatorSame :
          Distribution.indicator (algebra.signatureEvent term.event)
              (algebra.signature item) =
            Distribution.indicator (algebra.evaluate term.event) item := by
        unfold Distribution.indicator
        rw [algebra.signatureEvent_signature term.event item]
      rw [indicatorSame]

/-- Equal finite algebra signatures force equal values of every displayed
simple observable over that algebra. -/
theorem evaluate_eq_of_signature_eq {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra) {left right : α}
    (same : algebra.signature left = algebra.signature right) :
    observable.evaluate left = observable.evaluate right := by
  rw [← observable.signatureValue_signature left,
    ← observable.signatureValue_signature right, same]

/-- Exact integral of a displayed simple observable over a finite
distribution. -/
def expectation {α : Type} {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra)
    (distribution : Distribution α) : Coordinate :=
  distribution.expectation observable.evaluate

/-- The elementary simple-function integration formula: a finite sum of
coefficient times event probability. -/
theorem expectation_eq_sum {α : Type}
    {algebra : FiniteEventAlgebra α}
    (distribution : Distribution α) :
    ∀ observable : SimpleObservable algebra,
      observable.expectation distribution =
        (observable.map fun term =>
          distribution.probability (algebra.evaluate term.event) *
            term.coefficient).sum
  | [] => by
      unfold expectation
      simp only [evaluate, List.map_nil, List.sum_nil]
      exact distribution.expectation_constant 0
  | term :: remaining => by
      unfold expectation
      simp only [evaluate, List.map_cons, List.sum_cons]
      rw [distribution.expectation_add]
      have head : distribution.expectation (fun item =>
          Distribution.indicator (algebra.evaluate term.event) item *
            term.coefficient) =
          distribution.probability (algebra.evaluate term.event) *
            term.coefficient := by
        calc
          distribution.expectation (fun item =>
                Distribution.indicator (algebra.evaluate term.event) item *
                  term.coefficient) =
              distribution.expectation (fun item => term.coefficient *
                Distribution.indicator
                  (algebra.evaluate term.event) item) :=
            distribution.expectation_congr _ _ (fun item => by ring1)
          _ = distribution.probability (algebra.evaluate term.event) *
                term.coefficient := by
            rw [distribution.expectation_scale,
              distribution.expectation_indicator]
            ring1
      rw [head]
      exact congrArg
        (fun tail =>
          distribution.probability (algebra.evaluate term.event) *
              term.coefficient + tail)
        (expectation_eq_sum distribution remaining)

/-- Simple-observable expectation is recovered exactly from the finite
truth-signature distribution of its event algebra. -/
theorem expectation_eq_signatureDistribution_expectation {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra)
    (distribution : Distribution α) :
    observable.expectation distribution =
      (algebra.signatureDistribution distribution).expectation
        observable.signatureValue := by
  unfold expectation
  calc
    distribution.expectation observable.evaluate =
        distribution.expectation (fun item =>
          observable.signatureValue (algebra.signature item)) := by
      exact distribution.expectation_congr _ _ (fun item =>
        (observable.signatureValue_signature item).symm)
    _ = (algebra.signatureDistribution distribution).expectation
          observable.signatureValue :=
      (distribution.map_expectation algebra.signature
        observable.signatureValue).symm

/-- Equivalently, the unique displayed signature atoms and their consolidated
rational weights determine every simple-observable integral. -/
theorem expectation_eq_atomDistribution_expectation {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra)
    (distribution : Distribution α) :
    observable.expectation distribution =
      (algebra.atomDistribution distribution).expectation
        observable.signatureValue := by
  calc
    observable.expectation distribution =
        (algebra.signatureDistribution distribution).expectation
          observable.signatureValue :=
      observable.expectation_eq_signatureDistribution_expectation distribution
    _ = (algebra.atomDistribution distribution).expectation
          observable.signatureValue :=
      ((algebra.signatureDistribution distribution)
        |>.consolidate_evaluationEquivalent.expectation_eq
          observable.signatureValue).symm

/-- Sum of two displayed simple observables, implemented by finite list
concatenation. -/
def add {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra) : SimpleObservable algebra :=
  left ++ right

theorem evaluate_add {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra) (item : α) :
    (left.add right).evaluate item =
      left.evaluate item + right.evaluate item := by
  unfold add
  induction left with
  | nil => simp only [List.nil_append, evaluate, zero_add]
  | cons term remaining inductionHypothesis =>
      simp only [List.cons_append, evaluate]
      rw [inductionHypothesis]
      ring1

theorem expectation_add {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra)
    (distribution : Distribution α) :
    (left.add right).expectation distribution =
      left.expectation distribution + right.expectation distribution := by
  unfold expectation
  calc
    distribution.expectation (left.add right).evaluate =
        distribution.expectation (fun item =>
          left.evaluate item + right.evaluate item) :=
      distribution.expectation_congr _ _ (left.evaluate_add right)
    _ = distribution.expectation left.evaluate +
          distribution.expectation right.evaluate :=
      distribution.expectation_add left.evaluate right.evaluate

/-- Rational scaling of every displayed indicator coefficient. -/
def scale {α : Type} {algebra : FiniteEventAlgebra α}
    (factor : Coordinate) (observable : SimpleObservable algebra) :
    SimpleObservable algebra :=
  observable.map fun term =>
    { event := term.event
      coefficient := factor * term.coefficient }

theorem evaluate_scale {α : Type} {algebra : FiniteEventAlgebra α}
    (factor : Coordinate) (observable : SimpleObservable algebra)
    (item : α) :
    (observable.scale factor).evaluate item =
      factor * observable.evaluate item := by
  induction observable with
  | nil => simp only [scale, List.map_nil, evaluate, mul_zero]
  | cons term remaining inductionHypothesis =>
      unfold scale at inductionHypothesis
      simp only [scale, List.map_cons, evaluate]
      rw [inductionHypothesis]
      ring1

theorem expectation_scale {α : Type}
    {algebra : FiniteEventAlgebra α}
    (factor : Coordinate) (observable : SimpleObservable algebra)
    (distribution : Distribution α) :
    (observable.scale factor).expectation distribution =
      factor * observable.expectation distribution := by
  unfold expectation
  calc
    distribution.expectation (observable.scale factor).evaluate =
        distribution.expectation (fun item =>
          factor * observable.evaluate item) :=
      distribution.expectation_congr _ _
        (observable.evaluate_scale factor)
    _ = factor * distribution.expectation observable.evaluate :=
      distribution.expectation_scale factor observable.evaluate

/-- Additive inverse of a displayed simple observable. -/
def neg {α : Type} {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra) : SimpleObservable algebra :=
  observable.scale (-1)

theorem evaluate_neg {α : Type} {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra) (item : α) :
    observable.neg.evaluate item = -observable.evaluate item := by
  unfold neg
  rw [observable.evaluate_scale]
  ring1

theorem expectation_neg {α : Type} {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra)
    (distribution : Distribution α) :
    observable.neg.expectation distribution =
      -observable.expectation distribution := by
  unfold neg
  rw [observable.expectation_scale]
  ring1

/-- Difference of two displayed simple observables. -/
def sub {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra) : SimpleObservable algebra :=
  left.add right.neg

theorem evaluate_sub {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra) (item : α) :
    (left.sub right).evaluate item =
      left.evaluate item - right.evaluate item := by
  unfold sub
  rw [left.evaluate_add, right.evaluate_neg]
  ring1

theorem expectation_sub {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra)
    (distribution : Distribution α) :
    (left.sub right).expectation distribution =
      left.expectation distribution - right.expectation distribution := by
  unfold sub neg
  rw [left.expectation_add, right.expectation_scale]
  ring1

private def mulTerm {α : Type} {algebra : FiniteEventAlgebra α}
    (left : SimpleTerm algebra) (right : SimpleObservable algebra) :
    SimpleObservable algebra :=
  right.map fun term =>
    { event := algebra.intersection left.event term.event
      coefficient := left.coefficient * term.coefficient }

private theorem evaluate_mulTerm {α : Type}
    {algebra : FiniteEventAlgebra α} (left : SimpleTerm algebra) :
    ∀ (right : SimpleObservable algebra) (item : α),
      (mulTerm left right).evaluate item =
        (Distribution.indicator (algebra.evaluate left.event) item *
          left.coefficient) * right.evaluate item
  | [], item => by
      simp only [mulTerm, List.map_nil, evaluate, mul_zero]
  | term :: remaining, item => by
      simp only [mulTerm, List.map_cons, evaluate]
      unfold mulTerm at evaluate_mulTerm
      rw [evaluate_mulTerm left remaining item]
      unfold Distribution.indicator
      rw [algebra.evaluate_intersection]
      cases algebra.evaluate left.event item <;>
        cases algebra.evaluate term.event item <;>
        simp only [Bool.false_and, Bool.true_and] <;>
        ring1

/-- Product of two displayed simple observables.  Each output term uses the
explicit intersection code supplied by the finite event algebra. -/
def mul {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra) : SimpleObservable algebra :=
  left.flatMap fun term => mulTerm term right

theorem evaluate_mul {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra) (item : α) :
    (left.mul right).evaluate item =
      left.evaluate item * right.evaluate item := by
  induction left with
  | nil => simp only [mul, List.flatMap_nil, evaluate, zero_mul]
  | cons term remaining inductionHypothesis =>
      change evaluate (mulTerm term right ++ mul remaining right) item = _
      have appendEvaluation :=
        evaluate_add (mulTerm term right) (mul remaining right) item
      unfold add at appendEvaluation
      rw [appendEvaluation, evaluate_mulTerm, inductionHypothesis]
      simp only [evaluate]
      ring1

theorem expectation_mul {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : SimpleObservable algebra)
    (distribution : Distribution α) :
    (left.mul right).expectation distribution =
      distribution.expectation (fun item =>
        left.evaluate item * right.evaluate item) := by
  unfold expectation
  exact distribution.expectation_congr _ _ (left.evaluate_mul right)

end SimpleObservable

end FiniteMeasure
