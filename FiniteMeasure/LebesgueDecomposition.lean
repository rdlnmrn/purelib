import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ContentOperations
import FiniteMeasure.Singularity

/-!
# Finite constructive Lebesgue decomposition

Exact rational equality decides whether a payload has positive source mass.
That executable support event splits any target content into a part absolutely
continuous with respect to the source and a mutually singular remainder.
The decomposition is a finite partition of the displayed target table.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- The executable support of a finite content: an item is selected exactly
when its singleton event has nonzero rational content. -/
def supportEvent {α : Type} [DecidableEq α]
    (content : FiniteContent α) : α → Bool :=
  fun item => if content.measure (atomEvent item) = 0 then false else true

theorem supportEvent_eq_false_iff {α : Type} [DecidableEq α]
    (content : FiniteContent α) (item : α) :
    content.supportEvent item = false ↔
      content.measure (atomEvent item) = 0 := by
  unfold supportEvent
  by_cases zero : content.measure (atomEvent item) = 0
  · rw [if_pos zero]
    exact ⟨fun _ => zero, fun _ => rfl⟩
  · rw [if_neg zero]
    constructor
    · intro impossible
      nomatch impossible
    · intro equality
      exact (zero equality).elim

theorem supportEvent_eq_true_iff {α : Type} [DecidableEq α]
    (content : FiniteContent α) (item : α) :
    content.supportEvent item = true ↔
      content.measure (atomEvent item) ≠ 0 := by
  unfold supportEvent
  by_cases zero : content.measure (atomEvent item) = 0
  · rw [if_pos zero]
    constructor
    · intro impossible
      nomatch impossible
    · intro nonzero
      exact (nonzero zero).elim
  · rw [if_neg zero]
    exact ⟨fun _ => zero, fun _ => rfl⟩

/-- A finite content gives zero mass to the complement of its computed
support. -/
theorem measure_complement_supportEvent_eq_zero {α : Type}
    [DecidableEq α] (content : FiniteContent α) :
    content.measure (complementEvent content.supportEvent) = 0 := by
  have equal : EqualOffZeroWeightOn content.atoms
      (complementEvent content.supportEvent) (fun _ => false) := by
    intro atom member
    by_cases singletonZero :
        content.measure (atomEvent atom.item) = 0
    · apply Or.inl
      have selected : atomEvent atom.item atom.item = true := by
        unfold atomEvent
        simp only [decide_true]
      have bounded := atom_weight_le_eventWeight_of_mem member selected
      change atom.weight ≤ content.measure (atomEvent atom.item) at bounded
      rw [singletonZero] at bounded
      exact RFAP.ConstructiveFraction.le_antisymm
        atom.weight 0 bounded atom.nonnegative
    · apply Or.inr
      unfold complementEvent supportEvent
      rw [if_neg singletonZero]
      rfl
  calc
    content.measure (complementEvent content.supportEvent) =
        content.measure (fun _ => false) :=
      eventWeight_congr_off_zero content.atoms
        (complementEvent content.supportEvent) (fun _ => false) equal
    _ = 0 := content.measure_empty

/-- Splitting an event by another executable event is exactly additive. -/
theorem measure_intersection_add_complement {α : Type}
    (content : FiniteContent α) (event split : α → Bool) :
    content.measure (intersectionEvent event split) +
        content.measure
          (intersectionEvent event (complementEvent split)) =
      content.measure event := by
  unfold measure
  induction content.atoms with
  | nil =>
      change (0 : Coordinate) + 0 = 0
      ring1
  | cons atom remaining inductionHypothesis =>
      cases eventSelected : event atom.item <;>
        cases splitSelected : split atom.item <;>
        simp only [eventWeight, intersectionEvent, complementEvent,
          eventSelected, splitSelected, Bool.false_and, Bool.true_and,
          Bool.not_false, Bool.not_true, zero_add] <;>
        rw [← inductionHypothesis] <;>
        ring1

/-- The source-supported part of `target`. -/
def lebesgueRegularPart {α : Type} [DecidableEq α]
    (target source : FiniteContent α) : FiniteContent α :=
  target.restrict source.supportEvent

/-- The part of `target` carried outside the source support. -/
def lebesgueSingularPart {α : Type} [DecidableEq α]
    (target source : FiniteContent α) : FiniteContent α :=
  target.restrict (complementEvent source.supportEvent)

/-- The regular part is absolutely continuous with respect to the source. -/
theorem lebesgueRegularPart_absolutelyContinuous {α : Type}
    [DecidableEq α] (target source : FiniteContent α) :
    (target.lebesgueRegularPart source).AbsolutelyContinuous source := by
  intro event eventZero
  rw [lebesgueRegularPart, target.restrict_measure]
  calc
    target.measure (intersectionEvent event source.supportEvent) =
        target.measure (fun _ => false) := by
      apply target.measure_congr
      intro item
      cases selected : event item
      · simp only [intersectionEvent, selected, Bool.false_and]
      · have singletonLe : source.measure (atomEvent item) ≤
            source.measure event := by
          apply source.mono
          intro atom member atomSelected
          have same : atom.item = item := by
            unfold atomEvent at atomSelected
            exact of_decide_eq_true atomSelected
          simpa only [same] using selected
        have singletonZero : source.measure (atomEvent item) = 0 :=
          RFAP.ConstructiveFraction.le_antisymm _ _
            (eventZero ▸ singletonLe) (source.measure_nonneg _)
        unfold intersectionEvent supportEvent
        rw [selected, if_pos singletonZero]
        rfl
    _ = 0 := target.measure_empty

/-- The singular remainder is separated from the source by the computed
source support. -/
def lebesgueSingularPart_mutuallySingular {α : Type}
    [DecidableEq α] (target source : FiniteContent α) :
    MutuallySingular source (target.lebesgueSingularPart source) where
  separator := source.supportEvent
  left_outside_zero := source.measure_complement_supportEvent_eq_zero
  right_inside_zero := by
    rw [lebesgueSingularPart, target.restrict_measure]
    calc
      target.measure (intersectionEvent source.supportEvent
            (complementEvent source.supportEvent)) =
          target.measure (fun _ => false) := by
        apply target.measure_congr
        intro item
        cases selected : source.supportEvent item <;>
          unfold intersectionEvent complementEvent <;>
          rw [selected] <;> rfl
      _ = 0 := target.measure_empty

/-- The regular and singular parts reconstruct every target event exactly. -/
theorem measure_eq_lebesgueRegularPart_add_lebesgueSingularPart
    {α : Type} [DecidableEq α] (target source : FiniteContent α)
    (event : α → Bool) :
    target.measure event =
        (target.lebesgueRegularPart source).measure event +
      (target.lebesgueSingularPart source).measure event := by
  rw [lebesgueRegularPart, lebesgueSingularPart,
    target.restrict_measure, target.restrict_measure]
  exact (target.measure_intersection_add_complement
    event source.supportEvent).symm

/-- Data form of the finite Lebesgue decomposition theorem. -/
structure LebesgueDecomposition {α : Type}
    (target source : FiniteContent α) where
  regular : FiniteContent α
  singular : FiniteContent α
  measure_eq : ∀ event : α → Bool,
    target.measure event = regular.measure event + singular.measure event
  regular_absolutelyContinuous : regular.AbsolutelyContinuous source
  source_mutuallySingular_singular : MutuallySingular source singular

/-- The canonical executable finite Lebesgue decomposition. -/
def lebesgueDecomposition {α : Type} [DecidableEq α]
    (target source : FiniteContent α) :
    LebesgueDecomposition target source where
  regular := target.lebesgueRegularPart source
  singular := target.lebesgueSingularPart source
  measure_eq := target.measure_eq_lebesgueRegularPart_add_lebesgueSingularPart
    source
  regular_absolutelyContinuous :=
    target.lebesgueRegularPart_absolutelyContinuous source
  source_mutuallySingular_singular :=
    target.lebesgueSingularPart_mutuallySingular source

end FiniteContent

end FiniteMeasure
