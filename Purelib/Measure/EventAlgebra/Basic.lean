module
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Mixture.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Explicit finite event algebras

An event algebra here is finite presented data: an explicitly enumerated code
type, an executable interpretation of each code as a Boolean event, and
certified Boolean operations.  No powerset, sigma-algebra, generated closure,
or enumeration of an ambient carrier is formed.
-/

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a finite executable event-code algebra with its complete code list and Boolean evaluation laws.

The displayed list covers every code and code equality is decidable. Empty, universal, complement, union and
intersection operations retain codes in this same carrier with pointwise Boolean correctness certificates. -/
structure EventAlgebra (α : Type) where
  /-- The exact event-code carrier retained by this algebra. -/ Code : Type
  /-- The displayed finite list covering all event codes. -/ codes : List Code
  /-- Every code occurs in the retained enumeration. -/ listed : ∀ code, code ∈ codes
  /-- Executable decidable equality on the exact retained code carrier. -/ codeEq : (left right : Code) → Decidable
    (left = right)
  /-- Read each retained code as a Boolean event on payloads. -/ evaluate : Code → α → Bool
  /-- The retained code for the constantly false event. -/ empty : Code
  /-- The retained code for the constantly true event. -/ univ : Code
  /-- Construct the complement code in the same carrier. -/ complement : Code → Code
  /-- Construct the union code in the same carrier. -/ union : Code → Code → Code
  /-- Construct the intersection code in the same carrier. -/ intersection : Code → Code → Code
  /-- The retained empty code evaluates to false at every payload. -/ evaluate_empty : ∀ item, evaluate empty item =
    false
  /-- The retained universal code evaluates to true at every payload. -/ evaluate_univ : ∀ item, evaluate univ item =
    true
  /-- Complement code evaluation is Boolean negation of the original evaluation. -/ evaluate_complement : ∀ event item,
    evaluate (complement event) item = !(evaluate event item)
  /-- Union code evaluation is Boolean disjunction of the two original evaluations. -/ evaluate_union : ∀ left right
    item,
    evaluate (union left right) item =
      (evaluate left item || evaluate right item)
  /-- Intersection code evaluation is Boolean conjunction of the two original evaluations. -/ evaluate_intersection : ∀
    left right item,
    evaluate (intersection left right) item =
      (evaluate left item && evaluate right item)

constructive_injectivity EventAlgebra

namespace EventAlgebra

/-- Pull the retained event algebra back along a payload function while preserving its exact code carrier, enumeration
and operations. -/
def comap {α β : Type} (algebra : EventAlgebra β)
    (function : α → β) : EventAlgebra α where
  Code := algebra.Code
  codes := algebra.codes
  listed := algebra.listed
  codeEq := algebra.codeEq
  evaluate event item := algebra.evaluate event (function item)
  empty := algebra.empty
  univ := algebra.univ
  complement := algebra.complement
  union := algebra.union
  intersection := algebra.intersection
  evaluate_empty item := algebra.evaluate_empty (function item)
  evaluate_univ item := algebra.evaluate_univ (function item)
  evaluate_complement event item :=
    algebra.evaluate_complement event (function item)
  evaluate_union left right item :=
    algebra.evaluate_union left right (function item)
  evaluate_intersection left right item :=
    algebra.evaluate_intersection left right (function item)

/-- Evaluating a pulled-back code is original evaluation after the supplied payload map. -/
@[simp] theorem comap_evaluate {α β : Type}
    (algebra : EventAlgebra β) (function : α → β)
    (event : algebra.Code) (item : α) :
    (algebra.comap function).evaluate event item =
      algebra.evaluate event (function item) := rfl

/-- List a payload's Boolean evaluations in the exact retained event-code order. -/
def signature {α : Type} (algebra : EventAlgebra α)
    (item : α) : List Bool :=
  algebra.codes.map fun event => algebra.evaluate event item

/-- Search parallel code and Boolean lists for the first target code, returning false if either list runs out. -/
private def selectCode {Code : Type}
    (equal : (left right : Code) → Decidable (left = right))
    (target : Code) : List Code → List Bool → Bool
  | [], _ => false
  | _ :: _, [] => false
  | event :: remaining, selected :: selections =>
      match equal target event with
      | .isTrue _ => selected
      | .isFalse _ => selectCode equal target remaining selections

/-- Looking up a listed code in its parallel evaluation list recovers the exact target evaluation. -/
private theorem selectCode_map {Code α : Type}
    (equal : (left right : Code) → Decidable (left = right))
    (evaluate : Code → α → Bool) (target : Code) (item : α) :
    ∀ events : List Code, target ∈ events →
      selectCode equal target events
          (events.map fun event => evaluate event item) =
        evaluate target item
  | [], member => by
      cases member
  | event :: remaining, member => by
      cases decision : equal target event with
      | isTrue same =>
          subst event
          simp only [List.map_cons, selectCode, decision, -eq_self, -iff_self]
          rfl
      | isFalse different =>
          have tail : target ∈ remaining := by
            cases member with
            | head => exact (different rfl).elim
            | tail _ tailMember => exact tailMember
          simp only [List.map_cons, selectCode, decision, -eq_self, -iff_self]
          exact selectCode_map equal evaluate target item remaining tail

/-- Evaluate a retained event code on a Boolean signature by scanning the original complete code list.

Return the first matching code's Boolean entry, or false if the signature runs out. Decidable code equality and the
retained list determine the exact lookup. -/
def signatureEvent {α : Type} (algebra : EventAlgebra α)
    (event : algebra.Code) : List Bool → Bool :=
  let rec selectCodeHere : List algebra.Code → List Bool → Bool
    | [], _ => false
    | _ :: _, [] => false
    | candidate :: remaining, selected :: selections =>
        match algebra.codeEq event candidate with
        | .isTrue _ => selected
        | .isFalse _ => selectCodeHere remaining selections
  selectCodeHere algebra.codes

/-- The exposed signature lookup agrees with the direct parallel-list lookup on the same retained codes and values. -/
private theorem signatureEvent_eq_selectCode {α : Type}
    (algebra : EventAlgebra α) (event : algebra.Code)
    (values : List Bool) :
    algebra.signatureEvent event values =
      selectCode algebra.codeEq event algebra.codes values := by
  unfold signatureEvent
  generalize algebra.codes = codes
  induction codes generalizing values with
  | nil => cases values <;> rfl
  | cons candidate remaining ih =>
      cases values with
      | nil => rfl
      | cons selected selections =>
          cases decision : algebra.codeEq event candidate with
          | isTrue _ =>
              simp only [signatureEvent.selectCodeHere, selectCode, decision, -eq_self, -iff_self]
              rfl
          | isFalse _ =>
              simp only [signatureEvent.selectCodeHere, selectCode, decision, -eq_self, -iff_self]
              exact ih selections

/-- Reading a code from a payload's exact signature recovers its original Boolean event evaluation. -/
theorem signatureEvent_signature {α : Type}
    (algebra : EventAlgebra α) (event : algebra.Code) (item : α) :
    algebra.signatureEvent event (algebra.signature item) =
      algebra.evaluate event item := by
  rw [signatureEvent_eq_selectCode]
  exact selectCode_map algebra.codeEq algebra.evaluate event item algebra.codes
    (algebra.listed event)

/-- Payloads with equal retained signatures agree on every event code of the same algebra. -/
theorem evaluate_eq_of_signature_eq {α : Type}
    (algebra : EventAlgebra α) {left right : α}
    (same : algebra.signature left = algebra.signature right)
    (event : algebra.Code) :
    algebra.evaluate event left = algebra.evaluate event right := by
  rw [← algebra.signatureEvent_signature event left,
    ← algebra.signatureEvent_signature event right, same]
end EventAlgebra
end Purelib.Measure

end
