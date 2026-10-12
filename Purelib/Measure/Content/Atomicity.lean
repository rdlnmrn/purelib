module
public import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
/-!
# Atomicity of displayed finite contents

Every positive displayed finite content has a payload with positive singleton
mass.  Hence a content whose singleton events are all null has zero total,
and no displayed finite probability distribution is atomless.  This records
inside the theory the exact boundary separating it from nonatomic measure
spaces.
-/

@[expose] public section

namespace Purelib.Measure

/-- A finite nonnegative weighted list with positive total contains an occurrence of positive weight. -/
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

namespace Content

/-- Require zero content mass at every singleton payload. -/
def Atomless {α : Type} [DecidableEq α]
    (content : Content α) : Prop :=
  ∀ item : α, content.measure (atomEvent item) = 0

/-- Positive content total gives a positive-weight occurrence in its exact retained atom list. -/
theorem exists_positive_weight {α : Type} (content : Content α)
    (positive : 0 < content.total) :
    ∃ atom, atom ∈ content.atoms ∧ 0 < atom.weight :=
  exists_positive_weight_of_totalWeight_pos content.atoms positive

/-- Positive total content mass gives a payload with strictly positive singleton measurement.

A positive retained occurrence contributes to its own singleton event. Its weight
is bounded by that event measurement, so the selected payload has positive mass. -/
theorem exists_positive_singleton {α : Type} [DecidableEq α]
    (content : Content α) (positive : 0 < content.total) :
    ∃ item : α, 0 < content.measure (atomEvent item) := by
  rcases content.exists_positive_weight positive with
    ⟨atom, member, atomPositive⟩
  refine ⟨atom.item, ?_⟩
  have selected : atomEvent atom.item atom.item = true := by
    unfold atomEvent
    exact decide_eq_true rfl
  exact atomPositive.trans_le
    (atom_weight_le_eventWeight_of_mem member selected)

open Purelib.Data.Rat
/-- A finite content with all singleton masses zero has total mass zero.

Each retained occurrence is bounded by its own singleton measurement. The
atomless hypothesis forces every weight to vanish, and structural induction sums
those zero weights in the original retained list. -/
theorem total_eq_zero_of_atomless {α : Type} [DecidableEq α]
    (content : Content α) (atomless : content.Atomless) :
    content.total = 0 := by
  have rowZero : ∀ atom, atom ∈ content.atoms → atom.weight = 0 := by
    intro atom member
    have selected : atomEvent atom.item atom.item = true := by
      unfold atomEvent
      exact decide_eq_true rfl
    have atomLe := atom_weight_le_eventWeight_of_mem member selected
    change atom.weight ≤ content.measure (atomEvent atom.item) at atomLe
    rw [atomless atom.item] at atomLe
    exact Fraction.Order.Basic.Compatibility.le_antisymm _ _ atomLe atom.nonnegative
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

/-- A finite nonnegative content is atomless exactly when its total mass is zero. -/
theorem atomless_iff_total_eq_zero {α : Type} [DecidableEq α]
    (content : Content α) :
    content.Atomless ↔ content.total = 0 := by
  constructor
  · exact content.total_eq_zero_of_atomless
  · intro totalZero item
    apply Fraction.Order.Basic.Compatibility.le_antisymm
    · exact (content.measure_le_total (atomEvent item)).trans_eq totalZero
    · exact content.measure_nonneg (atomEvent item)

end Content

end Purelib.Measure

end
