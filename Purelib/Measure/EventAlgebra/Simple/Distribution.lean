module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.EventAlgebra.Basic
public import Purelib.Measure.EventAlgebra.Distribution
public import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

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
namespace SimpleObservable

open Purelib.Data.Rat in
/-- Take the exact distribution's expectation of the retained simple observable's payload evaluation. -/
def expectation {α : Type} {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra)
    (distribution : Distribution α) : Fraction.Rational :=
  distribution.expectation observable.evaluate

/-- Simple-observable expectation equals the finite sum of original coded-event probabilities times their retained
coefficients. -/
theorem expectation_eq_sum {α : Type}
    {algebra : EventAlgebra α}
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

/-- Simple-observable expectation is preserved by the exact signature law and retained signature evaluator. -/
theorem expectation_eq_signatureDistribution_expectation {α : Type}
    {algebra : EventAlgebra α}
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

/-- Simple-observable expectation is preserved by the consolidated algebra atom law and retained signature evaluator. -/
theorem expectation_eq_atomDistribution_expectation {α : Type}
    {algebra : EventAlgebra α}
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

/-- Adding retained simple observables adds their original expectations. -/
theorem expectation_add {α : Type} {algebra : EventAlgebra α}
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

open Purelib.Data.Rat in
/-- Scaling a retained simple observable scales its original expectation by the same factor. -/
theorem expectation_scale {α : Type}
    {algebra : EventAlgebra α}
    (factor : Fraction.Rational) (observable : SimpleObservable algebra)
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

/-- Negating a retained simple observable negates its original expectation. -/
theorem expectation_neg {α : Type} {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra)
    (distribution : Distribution α) :
    observable.neg.expectation distribution =
      -observable.expectation distribution := by
  unfold neg
  rw [observable.expectation_scale]
  ring1

/-- Subtracting retained simple observables subtracts their original expectations. -/
theorem expectation_sub {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra)
    (distribution : Distribution α) :
    (left.sub right).expectation distribution =
      left.expectation distribution - right.expectation distribution := by
  unfold sub neg
  rw [left.expectation_add, right.expectation_scale]
  ring1

/-- The retained simple-observable product has expectation equal to the expectation of the two original payload
evaluations multiplied. -/
theorem expectation_mul {α : Type} {algebra : EventAlgebra α}
    (left right : SimpleObservable algebra)
    (distribution : Distribution α) :
    (left.mul right).expectation distribution =
      distribution.expectation (fun item =>
        left.evaluate item * right.evaluate item) := by
  unfold expectation
  exact distribution.expectation_congr _ _ (left.evaluate_mul right)

end SimpleObservable

end Purelib.Measure

end
