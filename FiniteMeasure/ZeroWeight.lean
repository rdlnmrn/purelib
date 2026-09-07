import FiniteMeasure.Probability

/-!
# Equality away from displayed zero weight

This is a finite replacement for almost-everywhere reasoning.  It quantifies
only over the supplied list of weighted atoms: two evaluations may differ at
an atom only when that atom carries exactly zero rational weight.
-/

namespace FiniteMeasure

/-- Pointwise equality at every displayed atom of nonzero weight. -/
def EqualOffZeroWeightOn {α β : Type} (atoms : List (Weighted α))
    (left right : α → β) : Prop :=
  ∀ atom, atom ∈ atoms → atom.weight = 0 ∨ left atom.item = right atom.item

namespace EqualOffZeroWeightOn

theorem refl {α β : Type} (atoms : List (Weighted α)) (value : α → β) :
    EqualOffZeroWeightOn atoms value value := by
  intro atom member
  exact Or.inr rfl

theorem symm {α β : Type} {atoms : List (Weighted α)}
    {left right : α → β} (equal : EqualOffZeroWeightOn atoms left right) :
    EqualOffZeroWeightOn atoms right left := by
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  · exact Or.inr same.symm

theorem trans {α β : Type} {atoms : List (Weighted α)}
    {left middle right : α → β}
    (leftMiddle : EqualOffZeroWeightOn atoms left middle)
    (middleRight : EqualOffZeroWeightOn atoms middle right) :
    EqualOffZeroWeightOn atoms left right := by
  intro atom member
  rcases leftMiddle atom member with zero | first
  · exact Or.inl zero
  rcases middleRight atom member with zero | second
  · exact Or.inl zero
  · exact Or.inr (Eq.trans first second)

end EqualOffZeroWeightOn

/-- Exact finite expectations ignore displayed zero-weight discrepancies. -/
theorem expectationWeight_congr_off_zero {α : Type} :
    ∀ (atoms : List (Weighted α)) (left right : α → Coordinate),
      EqualOffZeroWeightOn atoms left right →
        Distribution.expectationWeight atoms left =
          Distribution.expectationWeight atoms right := by
  intro atoms left right equal
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tail : EqualOffZeroWeightOn remaining left right :=
        fun candidate member =>
          equal candidate (List.mem_cons_of_mem atom member)
      rcases equal atom List.mem_cons_self with zero | same
      · simp only [Distribution.expectationWeight, zero, zero_mul,
          inductionHypothesis tail]
      · simp only [Distribution.expectationWeight, same,
          inductionHypothesis tail]

/-- Exact finite event weights ignore changes on displayed zero-weight
atoms. -/
theorem eventWeight_congr_off_zero {α : Type} :
    ∀ (atoms : List (Weighted α)) (left right : α → Bool),
      EqualOffZeroWeightOn atoms left right →
        eventWeight atoms left = eventWeight atoms right := by
  intro atoms left right equal
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tail : EqualOffZeroWeightOn remaining left right :=
        fun candidate member =>
          equal candidate (List.mem_cons_of_mem atom member)
      have headEqual :
          (match left atom.item with
            | true => atom.weight
            | false => 0) =
          (match right atom.item with
            | true => atom.weight
            | false => 0) := by
        rcases equal atom List.mem_cons_self with zero | same
        · cases leftChoice : left atom.item <;>
            cases rightChoice : right atom.item <;>
            simp only [zero]
        · rw [same]
      change
        (match left atom.item with
          | true => atom.weight
          | false => 0) + eventWeight remaining left =
        (match right atom.item with
          | true => atom.weight
          | false => 0) + eventWeight remaining right
      rw [headEqual, inductionHypothesis tail]

/-- Every selected displayed atom is bounded by the total selected event
weight. -/
theorem atom_weight_le_eventWeight_of_mem {α : Type} :
    ∀ {atoms : List (Weighted α)} {event : α → Bool}
      {candidate : Weighted α},
      candidate ∈ atoms → event candidate.item = true →
        candidate.weight ≤ eventWeight atoms event
  | [], event, candidate, member, selected => by
      cases member
  | atom :: remaining, event, candidate, member, selected => by
      rcases List.mem_cons.mp member with head | tailMember
      · rw [head] at selected ⊢
        simp only [eventWeight, selected]
        exact le_add_of_nonneg_right (eventWeight_nonneg remaining event)
      · have tailBound := atom_weight_le_eventWeight_of_mem
          tailMember selected
        cases headSelected : event atom.item
        · simpa only [eventWeight, headSelected, zero_add] using tailBound
        · simp only [eventWeight, headSelected]
          exact tailBound.trans (le_add_of_nonneg_left atom.nonnegative)

/-- Equality away from one executable exceptional event on the displayed
atoms. -/
def EqualOutsideEventOn {α β : Type} (atoms : List (Weighted α))
    (exceptional : α → Bool) (left right : α → β) : Prop :=
  ∀ atom, atom ∈ atoms → exceptional atom.item = false →
    left atom.item = right atom.item

/-- A displayed event of exactly zero weight supports only zero-weight
discrepancies. -/
theorem equalOffZeroWeight_of_equalOutsideEvent {α β : Type}
    (atoms : List (Weighted α)) (exceptional : α → Bool)
    (left right : α → β)
    (zero : eventWeight atoms exceptional = 0)
    (outside : EqualOutsideEventOn atoms exceptional left right) :
    EqualOffZeroWeightOn atoms left right := by
  intro atom member
  cases selected : exceptional atom.item
  · exact Or.inr (outside atom member selected)
  · have weightLe := atom_weight_le_eventWeight_of_mem member selected
    rw [zero] at weightLe
    exact Or.inl (RFAP.ConstructiveFraction.le_antisymm _ _
      weightLe atom.nonnegative)

namespace Distribution

theorem expectation_congr_off_zero {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (equal : EqualOffZeroWeightOn distribution.atoms left right) :
    distribution.expectation left = distribution.expectation right :=
  expectationWeight_congr_off_zero distribution.atoms left right equal

theorem probability_congr_off_zero {α : Type}
    (distribution : Distribution α) (left right : α → Bool)
    (equal : EqualOffZeroWeightOn distribution.atoms left right) :
    distribution.probability left = distribution.probability right :=
  eventWeight_congr_off_zero distribution.atoms left right equal

theorem expectation_eq_of_equalOutsideZeroEvent {α : Type}
    (distribution : Distribution α) (exceptional : α → Bool)
    (left right : α → Coordinate)
    (zero : distribution.probability exceptional = 0)
    (outside : EqualOutsideEventOn distribution.atoms exceptional left right) :
    distribution.expectation left = distribution.expectation right := by
  apply distribution.expectation_congr_off_zero
  exact equalOffZeroWeight_of_equalOutsideEvent distribution.atoms exceptional
    left right zero outside

theorem probability_eq_of_equalOutsideZeroEvent {α : Type}
    (distribution : Distribution α) (exceptional left right : α → Bool)
    (zero : distribution.probability exceptional = 0)
    (outside : EqualOutsideEventOn distribution.atoms exceptional left right) :
    distribution.probability left = distribution.probability right := by
  apply distribution.probability_congr_off_zero
  exact equalOffZeroWeight_of_equalOutsideEvent distribution.atoms exceptional
    left right zero outside

end Distribution

end FiniteMeasure
