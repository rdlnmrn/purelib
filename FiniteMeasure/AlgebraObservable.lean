import FiniteMeasure.AtomicRepresentation

/-!
# Observables measurable through a finite event algebra

An algebra-observable carries its factorization through the complete finite
truth signature as data.  This is the constructive measurable-function
interface: evaluation on the ambient carrier is executable, and no
representative is selected from an equivalence class.
-/

namespace FiniteMeasure

/-- A rational observable together with an explicit evaluator on finite
event-algebra truth signatures. -/
structure AlgebraObservable {α : Type} (algebra : FiniteEventAlgebra α) where
  evaluate : α → Coordinate
  signatureValue : List Bool → Coordinate
  signatureValue_signature : ∀ item,
    signatureValue (algebra.signature item) = evaluate item

namespace AlgebraObservable

/-- An algebra-observable is constant on payloads with the same complete
truth signature. -/
theorem evaluate_eq_of_signature_eq {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : AlgebraObservable algebra) {left right : α}
    (same : algebra.signature left = algebra.signature right) :
    observable.evaluate left = observable.evaluate right := by
  rw [← observable.signatureValue_signature left,
    ← observable.signatureValue_signature right, same]

def constant {α : Type} (algebra : FiniteEventAlgebra α)
    (value : Coordinate) : AlgebraObservable algebra where
  evaluate _ := value
  signatureValue _ := value
  signatureValue_signature _item := rfl

/-- Every coded event indicator is measurable through its truth-signature
coordinate. -/
def indicator {α : Type} (algebra : FiniteEventAlgebra α)
    (event : algebra.Code) : AlgebraObservable algebra where
  evaluate := Distribution.indicator (algebra.evaluate event)
  signatureValue := Distribution.indicator (algebra.signatureEvent event)
  signatureValue_signature item := by
    unfold Distribution.indicator
    rw [algebra.signatureEvent_signature event item]

/-- Every displayed simple observable supplies the stronger explicit
signature factorization. -/
def ofSimple {α : Type} {algebra : FiniteEventAlgebra α}
    (observable : SimpleObservable algebra) : AlgebraObservable algebra where
  evaluate := observable.evaluate
  signatureValue := observable.signatureValue
  signatureValue_signature := observable.signatureValue_signature

/-- Postcomposition preserves finite algebra measurability. -/
def map {α : Type} {algebra : FiniteEventAlgebra α}
    (observable : AlgebraObservable algebra)
    (transform : Coordinate → Coordinate) : AlgebraObservable algebra where
  evaluate item := transform (observable.evaluate item)
  signatureValue signature := transform (observable.signatureValue signature)
  signatureValue_signature item := by
    rw [observable.signatureValue_signature]

def add {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : AlgebraObservable algebra) : AlgebraObservable algebra where
  evaluate item := left.evaluate item + right.evaluate item
  signatureValue signature :=
    left.signatureValue signature + right.signatureValue signature
  signatureValue_signature item := by
    rw [left.signatureValue_signature, right.signatureValue_signature]

def scale {α : Type} {algebra : FiniteEventAlgebra α}
    (factor : Coordinate) (observable : AlgebraObservable algebra) :
    AlgebraObservable algebra where
  evaluate item := factor * observable.evaluate item
  signatureValue signature := factor * observable.signatureValue signature
  signatureValue_signature item := by
    rw [observable.signatureValue_signature]

def mul {α : Type} {algebra : FiniteEventAlgebra α}
    (left right : AlgebraObservable algebra) : AlgebraObservable algebra where
  evaluate item := left.evaluate item * right.evaluate item
  signatureValue signature :=
    left.signatureValue signature * right.signatureValue signature
  signatureValue_signature item := by
    rw [left.signatureValue_signature, right.signatureValue_signature]

/-- Pulling back both the algebra and observable along an executable map
preserves the same truth-signature factorization. -/
def comap {α β : Type} {algebra : FiniteEventAlgebra β}
    (observable : AlgebraObservable algebra) (function : α → β) :
    AlgebraObservable (algebra.comap function) where
  evaluate item := observable.evaluate (function item)
  signatureValue := observable.signatureValue
  signatureValue_signature item :=
    observable.signatureValue_signature (function item)

/-- Change of variables to the displayed signature table. -/
theorem integral_eq_signatureContent_integral {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : AlgebraObservable algebra)
    (content : FiniteContent α) :
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

/-- The consolidated finite algebra atoms determine the integral of every
explicitly algebra-measurable rational observable. -/
theorem integral_eq_atomContent_integral {α : Type}
    {algebra : FiniteEventAlgebra α}
    (observable : AlgebraObservable algebra)
    (content : FiniteContent α) :
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

end FiniteMeasure
