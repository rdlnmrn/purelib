import FiniteMeasure.SignedContent
import FiniteMeasure.AbsoluteContinuity

/-!
# Mutual singularity of finite contents

Two finite contents are mutually singular when one executable Boolean event
separates their displayed mass.  Hahn certificates separate the computed
positive and negative Jordan contents exactly.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- An explicit event supports `left`, while its complement supports `right`.
-/
structure MutuallySingular {α : Type}
    (left right : FiniteContent α) where
  separator : α → Bool
  left_outside_zero : left.measure (complementEvent separator) = 0
  right_inside_zero : right.measure separator = 0

namespace MutuallySingular

def symm {α : Type} {left right : FiniteContent α}
    (singular : MutuallySingular left right) :
    MutuallySingular right left where
  separator := complementEvent singular.separator
  left_outside_zero := by
    calc
      right.measure (complementEvent (complementEvent singular.separator)) =
          right.measure singular.separator :=
        right.measure_congr _ _ (fun item => by
          unfold complementEvent
          cases singular.separator item <;> rfl)
      _ = 0 := singular.right_inside_zero
  right_inside_zero := singular.left_outside_zero

def of_left_total_eq_zero {α : Type} (left right : FiniteContent α)
    (zero : left.total = 0) : MutuallySingular left right where
  separator := fun _ => false
  left_outside_zero := by
    calc
      left.measure (complementEvent (fun _ : α => false)) =
          left.measure (fun _ => true) :=
        left.measure_congr _ _ (fun _ => rfl)
      _ = left.total := left.measure_univ
      _ = 0 := zero
  right_inside_zero := right.measure_empty

def of_right_total_eq_zero {α : Type} (left right : FiniteContent α)
    (zero : right.total = 0) : MutuallySingular left right :=
  (of_left_total_eq_zero right left zero).symm

/-- A content both absolutely continuous with respect to and singular from
another content must have zero total mass. -/
theorem left_total_eq_zero_of_absolutelyContinuous {α : Type}
    {left right : FiniteContent α}
    (singular : MutuallySingular left right)
    (continuous : left.AbsolutelyContinuous right) :
    left.total = 0 := by
  have insideZero : left.measure singular.separator = 0 :=
    continuous singular.separator singular.right_inside_zero
  calc
    left.total = left.measure singular.separator +
        left.measure (complementEvent singular.separator) :=
      (left.add_complement singular.separator).symm
    _ = 0 := by rw [insideZero, singular.left_outside_zero, zero_add]

end MutuallySingular

end FiniteContent

private theorem positivePart_complement_measure_eq_zero {α : Type}
    (event : α → Bool) :
    ∀ atoms : List (SignedWeighted α),
      (∀ atom, atom ∈ atoms → event atom.item = false → atom.weight ≤ 0) →
      eventWeight
        (atoms.map fun atom =>
          ⟨atom.item, positiveWeight atom.weight,
            positiveWeight_nonneg atom.weight⟩)
        (complementEvent event) = 0
  | [], unselected => rfl
  | atom :: remaining, unselected => by
      have tail : ∀ candidate, candidate ∈ remaining →
          event candidate.item = false → candidate.weight ≤ 0 :=
        fun candidate member selected =>
          unselected candidate (List.mem_cons_of_mem atom member) selected
      cases selected : event atom.item
      · simp only [List.map_cons, eventWeight, complementEvent, selected,
          Bool.not_false, positivePart_complement_measure_eq_zero event
            remaining tail]
        rw [positiveWeight_eq_zero_of_nonpos
          (unselected atom List.mem_cons_self selected), zero_add]
      · simp only [List.map_cons, eventWeight, complementEvent, selected,
          Bool.not_true, zero_add,
          positivePart_complement_measure_eq_zero event remaining tail]

private theorem negativePart_event_measure_eq_zero {α : Type}
    (event : α → Bool) :
    ∀ atoms : List (SignedWeighted α),
      (∀ atom, atom ∈ atoms → event atom.item = true → 0 ≤ atom.weight) →
      eventWeight
        (atoms.map SignedContent.negativePartAtom)
        event = 0
  | [], selectedNonnegative => rfl
  | atom :: remaining, selectedNonnegative => by
      have tail : ∀ candidate, candidate ∈ remaining →
          event candidate.item = true → 0 ≤ candidate.weight :=
        fun candidate member selected =>
          selectedNonnegative candidate
            (List.mem_cons_of_mem atom member) selected
      cases selected : event atom.item
      · simp only [List.map_cons, eventWeight,
          SignedContent.negativePartAtom, selected, zero_add,
          negativePart_event_measure_eq_zero event remaining tail]
      · simp only [List.map_cons, eventWeight,
          SignedContent.negativePartAtom, selected,
          negativePart_event_measure_eq_zero event remaining tail]
        rw [negativeWeight_eq_zero_of_nonneg
          (selectedNonnegative atom List.mem_cons_self selected), zero_add]

namespace SignedContent.HahnCertificate

/-- A Hahn certificate proves that the computed positive and negative Jordan
contents are mutually singular. -/
def positiveContent_mutuallySingular_negativeContent {α : Type}
    {content : SignedContent α}
    (certificate : SignedContent.HahnCertificate content) :
    FiniteContent.MutuallySingular
      content.positiveContent content.negativeContent where
  separator := certificate.positiveEvent
  left_outside_zero := by
    unfold SignedContent.positiveContent FiniteContent.measure
    exact positivePart_complement_measure_eq_zero
      certificate.positiveEvent content.atoms
      certificate.unselected_nonpositive
  right_inside_zero := by
    unfold SignedContent.negativeContent FiniteContent.measure
    exact negativePart_event_measure_eq_zero
      certificate.positiveEvent content.atoms
      certificate.selected_nonnegative

end SignedContent.HahnCertificate

end FiniteMeasure
