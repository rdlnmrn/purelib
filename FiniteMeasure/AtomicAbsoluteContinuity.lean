import FiniteMeasure.AbsoluteContinuity
import FiniteMeasure.Consolidation

/-!
# Atomic tests for finite absolute continuity

On displayed finite contents with decidable payload equality, absolute
continuity can be checked on singleton events alone.  A source-null event
forces every selected source singleton to be null; the singleton hypothesis
then forces the corresponding target rows to carry zero mass.
-/

namespace FiniteMeasure

namespace FiniteContent.AbsolutelyContinuous

/-- Eventwise absolute continuity implies the singleton zero-mass test. -/
theorem atom_zero {α : Type} [DecidableEq α]
    {target source : FiniteContent α}
    (continuous : target.AbsolutelyContinuous source) (item : α) :
    source.measure (atomEvent item) = 0 →
      target.measure (atomEvent item) = 0 :=
  continuous (atomEvent item)

/-- The singleton zero-mass test suffices for eventwise finite absolute
continuity. -/
theorem of_atom_zero {α : Type} [DecidableEq α]
    {target source : FiniteContent α}
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
        simpa only [same] using selected
      have sourceSingletonZero :
          source.measure (atomEvent atom.item) = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          (sourceEventZero ▸ singletonLe)
          (source.measure_nonneg (atomEvent atom.item))
      have targetSingletonZero := atomZero atom.item sourceSingletonZero
      have selfSelected : atomEvent atom.item atom.item = true := by
        unfold atomEvent
        simp only [decide_true]
      have atomLe := atom_weight_le_eventWeight_of_mem member selfSelected
      change atom.weight ≤ target.measure (atomEvent atom.item) at atomLe
      rw [targetSingletonZero] at atomLe
      exact Or.inl (RFAP.ConstructiveFraction.le_antisymm _ _
        atomLe atom.nonnegative)
  calc
    target.measure event = target.measure (fun _ => false) :=
      eventWeight_congr_off_zero target.atoms event (fun _ => false) equal
    _ = 0 := target.measure_empty

end FiniteContent.AbsolutelyContinuous

/-- Finite absolute continuity is equivalent to preservation of zero mass on
every executable singleton event. -/
theorem FiniteContent.absolutelyContinuous_iff_atom_zero {α : Type}
    [DecidableEq α] (target source : FiniteContent α) :
    target.AbsolutelyContinuous source ↔
      ∀ item : α,
        source.measure (atomEvent item) = 0 →
          target.measure (atomEvent item) = 0 :=
  ⟨fun continuous item => continuous.atom_zero item,
    FiniteContent.AbsolutelyContinuous.of_atom_zero⟩

/-- Two finite contents have the same null events exactly when their
singleton masses vanish at the same payloads. -/
theorem FiniteContent.sameNullEvents_iff_atom_zero_iff {α : Type}
    [DecidableEq α] (left right : FiniteContent α) :
    left.SameNullEvents right ↔
      ∀ item : α,
        left.measure (atomEvent item) = 0 ↔
          right.measure (atomEvent item) = 0 := by
  constructor
  · intro same item
    exact same.measure_eq_zero_iff (atomEvent item)
  · intro atoms
    constructor
    · apply FiniteContent.AbsolutelyContinuous.of_atom_zero
      intro item rightZero
      exact (atoms item).mpr rightZero
    · apply FiniteContent.AbsolutelyContinuous.of_atom_zero
      intro item leftZero
      exact (atoms item).mp leftZero

end FiniteMeasure
