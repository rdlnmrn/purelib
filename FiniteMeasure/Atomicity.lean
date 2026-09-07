import FiniteMeasure.RadonNikodymExistence

/-!
# Atomicity of displayed finite contents

Every positive displayed finite content has a payload with positive singleton
mass.  Hence a content whose singleton events are all null has zero total,
and no displayed finite probability distribution is atomless.  This records
inside the theory the exact boundary separating it from nonatomic measure
spaces.
-/

namespace FiniteMeasure

private theorem exists_positive_weight_of_totalWeight_pos {α : Type} :
    ∀ atoms : List (Weighted α), 0 < totalWeight atoms →
      ∃ atom, atom ∈ atoms ∧ 0 < atom.weight
  | [], positive => by
      simp only [totalWeight] at positive
      exact (positive.false).elim
  | atom :: remaining, positive => by
      by_cases zero : atom.weight = 0
      · have tailPositive : 0 < totalWeight remaining := by
          simpa only [totalWeight, zero, zero_add] using positive
        rcases exists_positive_weight_of_totalWeight_pos remaining
            tailPositive with ⟨candidate, member, candidatePositive⟩
        exact ⟨candidate, List.mem_cons_of_mem atom member,
          candidatePositive⟩
      · have atomPositive : 0 < atom.weight :=
          lt_of_le_of_ne atom.nonnegative (Ne.symm zero)
        exact ⟨atom, List.mem_cons_self, atomPositive⟩

namespace FiniteContent

/-- Every executable singleton event is null. -/
def Atomless {α : Type} [DecidableEq α]
    (content : FiniteContent α) : Prop :=
  ∀ item : α, content.measure (atomEvent item) = 0

/-- Positive total mass contains an explicitly displayed positive-weight
row. -/
theorem exists_positive_weight {α : Type} (content : FiniteContent α)
    (positive : 0 < content.total) :
    ∃ atom, atom ∈ content.atoms ∧ 0 < atom.weight :=
  exists_positive_weight_of_totalWeight_pos content.atoms positive

/-- Positive total mass therefore gives a payload whose singleton event has
positive rational content. -/
theorem exists_positive_singleton {α : Type} [DecidableEq α]
    (content : FiniteContent α) (positive : 0 < content.total) :
    ∃ item : α, 0 < content.measure (atomEvent item) := by
  rcases content.exists_positive_weight positive with
    ⟨atom, member, atomPositive⟩
  refine ⟨atom.item, ?_⟩
  have selected : atomEvent atom.item atom.item = true := by
    unfold atomEvent
    simp only [decide_true]
  exact atomPositive.trans_le
    (atom_weight_le_eventWeight_of_mem member selected)

/-- A displayed finite atomless content necessarily has zero total mass. -/
theorem total_eq_zero_of_atomless {α : Type} [DecidableEq α]
    (content : FiniteContent α) (atomless : content.Atomless) :
    content.total = 0 := by
  have rowZero : ∀ atom, atom ∈ content.atoms → atom.weight = 0 := by
    intro atom member
    have selected : atomEvent atom.item atom.item = true := by
      unfold atomEvent
      simp only [decide_true]
    have atomLe := atom_weight_le_eventWeight_of_mem member selected
    change atom.weight ≤ content.measure (atomEvent atom.item) at atomLe
    rw [atomless atom.item] at atomLe
    exact RFAP.ConstructiveFraction.le_antisymm _ _ atomLe atom.nonnegative
  have totalWeightZero : ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms → atom.weight = 0) →
        totalWeight atoms = 0 := by
    intro atoms
    induction atoms with
    | nil =>
        intro _
        rfl
    | cons atom remaining inductionHypothesis =>
        intro rowsZero
        rw [totalWeight, rowsZero atom List.mem_cons_self, zero_add]
        apply inductionHypothesis
        intro candidate member
        exact rowsZero candidate (List.mem_cons_of_mem atom member)
  exact totalWeightZero content.atoms rowZero

/-- Zero total mass is equivalent to nullity of every singleton event. -/
theorem atomless_iff_total_eq_zero {α : Type} [DecidableEq α]
    (content : FiniteContent α) :
    content.Atomless ↔ content.total = 0 := by
  constructor
  · exact content.total_eq_zero_of_atomless
  · intro totalZero item
    apply RFAP.ConstructiveFraction.le_antisymm
    · exact (content.measure_le_total (atomEvent item)).trans_eq totalZero
    · exact content.measure_nonneg (atomEvent item)

end FiniteContent

namespace Distribution

/-- Every displayed finite probability distribution has a payload with
positive singleton probability. -/
theorem exists_positive_singleton {α : Type} [DecidableEq α]
    (distribution : Distribution α) :
    ∃ item : α, 0 < distribution.probability (atomEvent item) := by
  exact distribution.toFiniteContent.exists_positive_singleton
    (by rw [distribution.toFiniteContent_total]; decide)

/-- There is no atomless displayed finite probability distribution. -/
theorem not_atomless {α : Type} [DecidableEq α]
    (distribution : Distribution α) :
    ¬distribution.toFiniteContent.Atomless := by
  intro atomless
  have totalZero :=
    distribution.toFiniteContent.total_eq_zero_of_atomless atomless
  rw [distribution.toFiniteContent_total] at totalZero
  exact (by decide : (1 : Coordinate) ≠ 0) totalZero

end Distribution

end FiniteMeasure
