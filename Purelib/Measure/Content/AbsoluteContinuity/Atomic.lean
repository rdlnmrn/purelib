module
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.AlmostEverywhere
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Atomic tests for finite absolute continuity

On displayed finite contents with decidable payload equality, absolute
continuity can be checked on singleton events alone.  A source-null event
forces every selected source singleton to be null; the singleton hypothesis
then forces the corresponding target rows to carry zero mass.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content.AbsolutelyContinuous

/-- Absolute continuity transfers zero mass at each exact singleton payload from source to target. -/
theorem atom_zero {α : Type} [DecidableEq α]
    {target source : Content α}
    (continuous : target.AbsolutelyContinuous source) (item : α) :
    source.measure (atomEvent item) = 0 →
      target.measure (atomEvent item) = 0 :=
  continuous (atomEvent item)

open Purelib.Data.Rat in
/-- Transfer of zero singleton masses gives absolute continuity of the two finite contents.

For each source-null event, every selected source occurrence has zero singleton
mass. The singleton hypothesis transfers those equalities to the target. Each
selected target occurrence then has zero weight in the original finite sum. -/
theorem of_atom_zero {α : Type} [DecidableEq α]
    {target source : Content α}
    (atomZero : ∀ item : α,
      source.measure (atomEvent item) = 0 →
        target.measure (atomEvent item) = 0) :
    target.AbsolutelyContinuous source := by
  intro event sourceEventZero
  have equal : EqualOffZeroWeightOn target.atoms event (fun _ => false) := by
    intro atom member
    cases selected : event atom.item
    · exact Or.inr rfl
    · have singletonLe : source.measure (atomEvent atom.item) ≤
          source.measure event := by
        apply source.mono
        intro sourceAtom sourceMember singletonSelected
        have same : sourceAtom.item = atom.item := by
          unfold atomEvent at singletonSelected
          exact of_decide_eq_true singletonSelected
        rw [same]
        exact selected
      have sourceSingletonZero :
          source.measure (atomEvent atom.item) = 0 :=
        Fraction.Order.Basic.Compatibility.le_antisymm _ _
          (sourceEventZero ▸ singletonLe)
          (source.measure_nonneg (atomEvent atom.item))
      have targetSingletonZero := atomZero atom.item sourceSingletonZero
      have selfSelected : atomEvent atom.item atom.item = true := by
        unfold atomEvent
        exact decide_eq_true rfl
      have atomLe := atom_weight_le_eventWeight_of_mem member selfSelected
      change atom.weight ≤ target.measure (atomEvent atom.item) at atomLe
      rw [targetSingletonZero] at atomLe
      exact Or.inl (Fraction.Order.Basic.Compatibility.le_antisymm _ _
        atomLe atom.nonnegative)
  calc
    target.measure event = target.measure (fun _ => false) :=
      eventWeight_congr_off_zero target.atoms event (fun _ => false) equal
    _ = 0 := target.measure_empty

end Content.AbsolutelyContinuous

/-- Finite content absolute continuity is equivalent to transfer of zero mass at every singleton payload. -/
theorem Content.absolutelyContinuous_iff_atom_zero {α : Type}
    [DecidableEq α] (target source : Content α) :
    target.AbsolutelyContinuous source ↔
      ∀ item : α,
        source.measure (atomEvent item) = 0 →
          target.measure (atomEvent item) = 0 :=
  ⟨fun continuous item => continuous.atom_zero item,
    Content.AbsolutelyContinuous.of_atom_zero⟩

/-- Two finite contents have the same null events exactly when their singleton masses vanish at the same payloads. -/
theorem Content.sameNullEvents_iff_atom_zero_iff {α : Type}
    [DecidableEq α] (left right : Content α) :
    left.SameNullEvents right ↔
      ∀ item : α,
        left.measure (atomEvent item) = 0 ↔
          right.measure (atomEvent item) = 0 := by
  constructor
  · intro same item
    exact same.measure_eq_zero_iff (atomEvent item)
  · intro atoms
    constructor
    · apply Content.AbsolutelyContinuous.of_atom_zero
      intro item rightZero
      exact (atoms item).mpr rightZero
    · apply Content.AbsolutelyContinuous.of_atom_zero
      intro item leftZero
      exact (atoms item).mp leftZero

end Purelib.Measure
