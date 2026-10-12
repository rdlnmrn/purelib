module
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Singularity
import Purelib.Measure.SignedContent.Basic
public import Purelib.Measure.SignedContent.Hahn.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.PositiveNegativePart
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.Basic

section
/-!
# Mutual singularity of finite contents

Two finite contents are mutually singular when one executable Boolean event
separates their displayed mass.  Hahn certificates separate the computed
positive and negative Jordan contents exactly.
-/

@[expose] public section

namespace Purelib.Measure

section
open Purelib
/-- The positive parts give zero mass outside an event where all excluded signed occurrences are nonpositive.

The supplied sign witnesses apply to every retained occurrence outside the event, so their original positive weights
vanish individually. -/
private theorem positivePart_complement_measure_eq_zero {α : Type}
    (event : α → Bool) :
    ∀ atoms : List (SignedWeighted α),
      (∀ atom, atom ∈ atoms → event atom.item = false → atom.weight ≤ 0) →
      eventWeight
        (atoms.map fun atom =>
          ⟨atom.item, Data.Rat.positiveWeight atom.weight,
            Data.Rat.positiveWeight_nonneg atom.weight⟩)
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
        rw [Data.Rat.positiveWeight_eq_zero_of_nonpos
          (unselected atom List.mem_cons_self selected), zero_add]
      · simp only [List.map_cons, eventWeight, complementEvent, selected,
          Bool.not_true, zero_add,
          positivePart_complement_measure_eq_zero event remaining tail, -eq_self, -iff_self]
        rfl

/-- The negative parts give zero mass inside an event where all selected signed occurrences are nonnegative.

The supplied sign witnesses apply to every retained selected occurrence, so their original negative weights vanish
individually. -/
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
          negativePart_event_measure_eq_zero event remaining tail, -eq_self, -iff_self]
        rfl
      · simp only [List.map_cons, eventWeight,
          SignedContent.negativePartAtom, selected,
          negativePart_event_measure_eq_zero event remaining tail]
        rw [Data.Rat.negativeWeight_eq_zero_of_nonneg
          (selectedNonnegative atom List.mem_cons_self selected), zero_add]

end

namespace SignedContent.HahnCertificate

/-- Use the retained Hahn event to separate the exact positive and negative contents.

The original sign certificates make the positive part vanish outside that event and the negative part vanish inside it.
-/
def positiveContent_mutuallySingular_negativeContent {α : Type}
    {content : SignedContent α}
    (certificate : SignedContent.HahnCertificate content) :
    Content.MutuallySingular
      content.positiveContent content.negativeContent where
  separator := certificate.positiveEvent
  left_outside_zero := by
    unfold SignedContent.positiveContent Content.measure
    exact positivePart_complement_measure_eq_zero
      certificate.positiveEvent content.atoms
      certificate.unselected_nonpositive
  right_inside_zero := by
    unfold SignedContent.negativeContent Content.measure
    exact negativePart_event_measure_eq_zero
      certificate.positiveEvent content.atoms
      certificate.selected_nonnegative

end SignedContent.HahnCertificate

end Purelib.Measure

end
