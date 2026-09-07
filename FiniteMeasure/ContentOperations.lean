import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Valuation
import FiniteMeasure.AtomOperations

/-!
# Finite restriction and pushforward

Restriction and pushforward are direct transformations of displayed weighted
lists.  Their measure identities are finite recursive calculations over
executable Boolean events.
-/

namespace FiniteMeasure

/-- Retain exactly the displayed atoms selected by one executable event. -/
def restrictAtoms {α : Type} :
    List (Weighted α) → (α → Bool) → List (Weighted α)
  | [], _ => []
  | atom :: remaining, event =>
      if event atom.item then atom :: restrictAtoms remaining event
      else restrictAtoms remaining event

theorem totalWeight_restrictAtoms {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool),
      totalWeight (restrictAtoms atoms event) = eventWeight atoms event
  | [], event => rfl
  | atom :: remaining, event => by
      cases selected : event atom.item <;>
        simp only [restrictAtoms, selected, ↓reduceIte, totalWeight,
          eventWeight, Bool.false_eq_true, totalWeight_restrictAtoms,
          zero_add]

theorem eventWeight_restrictAtoms {α : Type} :
    ∀ (atoms : List (Weighted α)) (condition event : α → Bool),
      eventWeight (restrictAtoms atoms condition) event =
        eventWeight atoms (intersectionEvent event condition)
  | [], condition, event => rfl
  | atom :: remaining, condition, event => by
      cases conditionSelected : condition atom.item <;>
        cases eventSelected : event atom.item <;>
        simp only [restrictAtoms, conditionSelected, ↓reduceIte, eventWeight,
          eventSelected, intersectionEvent, Bool.false_eq_true,
          Bool.false_and, Bool.and_false, Bool.true_and, zero_add,
          eventWeight_restrictAtoms remaining condition event]

/-- Map every displayed payload while retaining its exact rational weight. -/
def mapAtoms {α β : Type} (function : α → β) :
    List (Weighted α) → List (Weighted β)
  | [] => []
  | atom :: remaining =>
      { item := function atom.item
        weight := atom.weight
        nonnegative := atom.nonnegative } ::
        mapAtoms function remaining

theorem totalWeight_mapAtoms {α β : Type} (function : α → β) :
    ∀ atoms : List (Weighted α),
      totalWeight (mapAtoms function atoms) = totalWeight atoms
  | [] => rfl
  | atom :: remaining => by
      simp only [mapAtoms, totalWeight, totalWeight_mapAtoms function remaining]

theorem eventWeight_mapAtoms {α β : Type} (function : α → β) :
    ∀ (atoms : List (Weighted α)) (event : β → Bool),
      eventWeight (mapAtoms function atoms) event =
        eventWeight atoms (fun item => event (function item))
  | [], event => rfl
  | atom :: remaining, event => by
      cases selected : event (function atom.item) <;>
        simp only [mapAtoms, eventWeight, selected,
          eventWeight_mapAtoms function remaining event]

/-- Cartesian product of two displayed finite atom lists. -/
def productAtoms {α β : Type} :
    List (Weighted α) → List (Weighted β) → List (Weighted (α × β))
  | [], _ => []
  | atom :: remaining, right =>
      scaleAtoms atom.weight atom.nonnegative
          (mapAtoms (fun rightItem => (atom.item, rightItem)) right) ++
        productAtoms remaining right

theorem totalWeight_productAtoms {α β : Type} :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      totalWeight (productAtoms left right) =
        totalWeight left * totalWeight right
  | [], right => by
      simp only [productAtoms, totalWeight, zero_mul]
  | atom :: remaining, right => by
      rw [productAtoms, totalWeight_append, totalWeight_scaleAtoms,
        totalWeight_mapAtoms, totalWeight_productAtoms remaining right]
      dsimp only [totalWeight]
      ring1

theorem eventWeight_productAtoms_rectangle {α β : Type} :
    ∀ (left : List (Weighted α)) (right : List (Weighted β))
      (leftEvent : α → Bool) (rightEvent : β → Bool),
      eventWeight (productAtoms left right)
          (fun pair => leftEvent pair.1 && rightEvent pair.2) =
        eventWeight left leftEvent * eventWeight right rightEvent
  | [], right, leftEvent, rightEvent => by
      simp only [productAtoms, eventWeight, zero_mul]
  | atom :: remaining, right, leftEvent, rightEvent => by
      rw [productAtoms, eventWeight_append, eventWeight_scaleAtoms,
        eventWeight_mapAtoms,
        eventWeight_productAtoms_rectangle remaining right]
      cases selected : leftEvent atom.item
      · have combinedWeightZero :
            eventWeight right
                (fun rightItem =>
                  leftEvent atom.item && rightEvent rightItem) = 0 :=
          calc
            eventWeight right
                  (fun rightItem =>
                    leftEvent atom.item && rightEvent rightItem) =
                eventWeight right (fun _ => false) :=
              eventWeight_congr right _ _ (fun rightItem => by
                rw [selected]
                rfl)
            _ = 0 := FiniteContent.measure_empty ⟨right⟩
        rw [combinedWeightZero]
        simp only [selected, eventWeight, mul_zero, zero_add]
      · have combinedWeightEqual :
            eventWeight right
                (fun rightItem =>
                  leftEvent atom.item && rightEvent rightItem) =
              eventWeight right rightEvent :=
          eventWeight_congr right _ _ (fun rightItem => by
            rw [selected]
            rfl)
        rw [combinedWeightEqual]
        simp only [selected, eventWeight]
        ring1

namespace FiniteContent

/-- Multiply every displayed content weight by a nonnegative rational
factor. -/
def scale {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (nonnegative : 0 ≤ factor) : FiniteContent α :=
  ⟨scaleAtoms factor nonnegative content.atoms⟩

theorem scale_total {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (nonnegative : 0 ≤ factor) :
    (content.scale factor nonnegative).total = factor * content.total :=
  totalWeight_scaleAtoms factor nonnegative content.atoms

theorem scale_measure {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (event : α → Bool) :
    (content.scale factor nonnegative).measure event =
      factor * content.measure event :=
  eventWeight_scaleAtoms factor nonnegative content.atoms event

/-- Concatenate two displayed finite content tables without identifying
equal payloads. -/
def append {α : Type} (left right : FiniteContent α) : FiniteContent α :=
  ⟨left.atoms ++ right.atoms⟩

theorem append_total {α : Type} (left right : FiniteContent α) :
    (left.append right).total = left.total + right.total :=
  totalWeight_append left.atoms right.atoms

theorem append_measure {α : Type} (left right : FiniteContent α)
    (event : α → Bool) :
    (left.append right).measure event =
      left.measure event + right.measure event :=
  eventWeight_append left.atoms right.atoms event

/-- Restrict a displayed finite content to one executable event. -/
def restrict {α : Type} (content : FiniteContent α) (event : α → Bool) :
    FiniteContent α :=
  ⟨restrictAtoms content.atoms event⟩

theorem restrict_total {α : Type} (content : FiniteContent α)
    (event : α → Bool) :
    (content.restrict event).total = content.measure event :=
  totalWeight_restrictAtoms content.atoms event

theorem restrict_measure {α : Type} (content : FiniteContent α)
    (condition event : α → Bool) :
    (content.restrict condition).measure event =
      content.measure (intersectionEvent event condition) :=
  eventWeight_restrictAtoms content.atoms condition event

/-- Exact finite pushforward of a displayed content. -/
def map {α β : Type} (content : FiniteContent α) (function : α → β) :
    FiniteContent β :=
  ⟨mapAtoms function content.atoms⟩

theorem map_total {α β : Type} (content : FiniteContent α)
    (function : α → β) :
    (content.map function).total = content.total :=
  totalWeight_mapAtoms function content.atoms

theorem map_measure {α β : Type} (content : FiniteContent α)
    (function : α → β) (event : β → Bool) :
    (content.map function).measure event =
      content.measure (fun item => event (function item)) :=
  eventWeight_mapAtoms function content.atoms event

/-- Cartesian product of two displayed finite contents. -/
def product {α β : Type} (left : FiniteContent α)
    (right : FiniteContent β) : FiniteContent (α × β) :=
  ⟨productAtoms left.atoms right.atoms⟩

theorem product_total {α β : Type} (left : FiniteContent α)
    (right : FiniteContent β) :
    (left.product right).total = left.total * right.total :=
  totalWeight_productAtoms left.atoms right.atoms

/-- Rectangular finite contents factor exactly. -/
theorem product_measure_rectangle {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (leftEvent : α → Bool) (rightEvent : β → Bool) :
    (left.product right).measure
        (fun pair => leftEvent pair.1 && rightEvent pair.2) =
      left.measure leftEvent * right.measure rightEvent :=
  eventWeight_productAtoms_rectangle left.atoms right.atoms
    leftEvent rightEvent

end FiniteContent

end FiniteMeasure
