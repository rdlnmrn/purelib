module
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.EventAlgebra.Basic
public import Purelib.Measure.EventAlgebra.Simple.Basic
public import Purelib.Measure.EventAlgebra.Content
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observables measurable through a finite event algebra

An algebra-observable carries its factorization through the complete finite
truth signature as data.  This is the constructive measurable-function
interface: evaluation on the ambient carrier is executable, and no
representative is selected from an equivalence class.
-/

@[expose] public section

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a rational observable together with its exact evaluation through the original finite event signature.

The signature function is defined on Boolean lists and is certified to recover the original observable on every
payload's actual algebra signature. -/
structure AlgebraObservable {α : Type} (algebra : EventAlgebra α) where
  /-- The exact rational observable on original payloads. -/ evaluate : α → Fraction.Rational
  /-- The retained rational evaluator on Boolean signature lists. -/ signatureValue : List Bool → Fraction.Rational
  /-- Evaluation of every actual original signature recovers its payload's observable value. -/ signatureValue_signature
    : ∀ item,
    signatureValue (algebra.signature item) = evaluate item

constructive_injectivity AlgebraObservable

section
open Purelib.Data.Rat

end

namespace AlgebraObservable

/-- Payloads with equal original algebra signatures have equal observable values. -/
theorem evaluate_eq_of_signature_eq {α : Type}
    {algebra : EventAlgebra α}
    (observable : AlgebraObservable algebra) {left right : α}
    (same : algebra.signature left = algebra.signature right) :
    observable.evaluate left = observable.evaluate right := by
  rw [← observable.signatureValue_signature left,
    ← observable.signatureValue_signature right, same]

open Purelib.Data.Rat in
/-- Represent a constant rational observable by the same constant on all signatures. -/
def constant {α : Type} (algebra : EventAlgebra α)
    (value : Fraction.Rational) : AlgebraObservable algebra where
  evaluate _ := value
  signatureValue _ := value
  signatureValue_signature _item := rfl

/-- Represent a coded event indicator through the exact corresponding signature event. -/
def indicator {α : Type} (algebra : EventAlgebra α)
    (event : algebra.Code) : AlgebraObservable algebra where
  evaluate := Distribution.indicator (algebra.evaluate event)
  signatureValue := Distribution.indicator (algebra.signatureEvent event)
  signatureValue_signature item := by
    unfold Distribution.indicator
    rw [algebra.signatureEvent_signature event item]

/-- Retain a simple observable's original evaluation and certified signature evaluation as an algebra observable. -/
def ofSimple {α : Type} {algebra : EventAlgebra α}
    (observable : SimpleObservable algebra) : AlgebraObservable algebra where
  evaluate := observable.evaluate
  signatureValue := observable.signatureValue
  signatureValue_signature := observable.signatureValue_signature

open Purelib.Data.Rat in
/-- Apply the same scalar transform to the original payload and signature evaluations. -/
def map {α : Type} {algebra : EventAlgebra α}
    (observable : AlgebraObservable algebra)
    (transform : Fraction.Rational → Fraction.Rational) : AlgebraObservable algebra where
  evaluate item := transform (observable.evaluate item)
  signatureValue signature := transform (observable.signatureValue signature)
  signatureValue_signature item := by
    rw [observable.signatureValue_signature]

/-- Add two observables on the same original algebra using their retained signature evaluations. -/
def add {α : Type} {algebra : EventAlgebra α}
    (left right : AlgebraObservable algebra) : AlgebraObservable algebra where
  evaluate item := left.evaluate item + right.evaluate item
  signatureValue signature :=
    left.signatureValue signature + right.signatureValue signature
  signatureValue_signature item := by
    rw [left.signatureValue_signature, right.signatureValue_signature]

open Purelib.Data.Rat in
/-- Scale an observable's payload and signature evaluations by the same rational factor. -/
def scale {α : Type} {algebra : EventAlgebra α}
    (factor : Fraction.Rational) (observable : AlgebraObservable algebra) :
    AlgebraObservable algebra where
  evaluate item := factor * observable.evaluate item
  signatureValue signature := factor * observable.signatureValue signature
  signatureValue_signature item := by
    rw [observable.signatureValue_signature]

/-- Multiply two observables on the same original algebra using their retained signature evaluations. -/
def mul {α : Type} {algebra : EventAlgebra α}
    (left right : AlgebraObservable algebra) : AlgebraObservable algebra where
  evaluate item := left.evaluate item * right.evaluate item
  signatureValue signature :=
    left.signatureValue signature * right.signatureValue signature
  signatureValue_signature item := by
    rw [left.signatureValue_signature, right.signatureValue_signature]

/-- Pull an observable and its algebra back along the supplied function while retaining the original signature
evaluator. -/
def comap {α β : Type} {algebra : EventAlgebra β}
    (observable : AlgebraObservable algebra) (function : α → β) :
    AlgebraObservable (algebra.comap function) where
  evaluate item := observable.evaluate (function item)
  signatureValue := observable.signatureValue
  signatureValue_signature item :=
    observable.signatureValue_signature (function item)

/-- The original observable integral equals its signature-value integral under the exact signature content. -/
theorem integral_eq_signatureContent_integral {α : Type}
    {algebra : EventAlgebra α}
    (observable : AlgebraObservable algebra)
    (content : Content α) :
    content.integral observable.evaluate =
      (algebra.signatureContent content).integral
        observable.signatureValue := by
  calc
    content.integral observable.evaluate =
        content.integral (fun item =>
          observable.signatureValue (algebra.signature item)) := by
      exact content.integral_congr _ _ (fun item =>
        (observable.signatureValue_signature item).symm)
    _ = (algebra.signatureContent content).integral
          observable.signatureValue :=
      (algebra.signatureContent_integral content
        observable.signatureValue).symm

/-- The original observable integral equals its signature-value integral under the consolidated algebra atom content. -/
theorem integral_eq_atomContent_integral {α : Type}
    {algebra : EventAlgebra α}
    (observable : AlgebraObservable algebra)
    (content : Content α) :
    content.integral observable.evaluate =
      (algebra.atomContent content).integral observable.signatureValue := by
  calc
    content.integral observable.evaluate =
        content.integral (fun item =>
          observable.signatureValue (algebra.signature item)) := by
      exact content.integral_congr _ _ (fun item =>
        (observable.signatureValue_signature item).symm)
    _ = (algebra.atomContent content).integral observable.signatureValue :=
      algebra.integral_eq_atomContent_integral content
        observable.signatureValue

end AlgebraObservable

end Purelib.Measure
