import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.AbsoluteContinuity
import FiniteMeasure.ContentEquivalence

/-!
# Finite Radon--Nikodym existence

For arbitrary displayed finite contents with decidable payload equality, the
union of their payload tables can be consolidated into a duplicate-free key
list.  Assigning each key its exact singleton mass gives aligned source and
target rows.  Absolute continuity supplies the rowwise zero implication, so
the quotient-density algorithm yields a Radon--Nikodym witness.

The proof below includes the finite histogram reconstruction lemma: summing
singleton masses over any duplicate-free key list covering a displayed atom
table recovers every rational integral.
-/

namespace FiniteMeasure

/-- A payload occurs in a displayed weighted key list. -/
def PayloadPresent {α : Type} (item : α) (atoms : List (Weighted α)) : Prop :=
  ∃ atom, atom ∈ atoms ∧ atom.item = item

private theorem payloadPresent_insertWeighted_self {α : Type}
    [DecidableEq α] (atom : Weighted α) :
    ∀ atoms : List (Weighted α),
      PayloadPresent atom.item (insertWeighted atom atoms)
  | [] => by
      exact ⟨atom, List.mem_cons_self, rfl⟩
  | current :: remaining => by
      by_cases same : atom.item = current.item
      · simp only [insertWeighted, same, ↓reduceDIte]
        exact ⟨_, List.mem_cons_self, rfl⟩
      · simp only [insertWeighted, same, ↓reduceDIte]
        rcases payloadPresent_insertWeighted_self atom remaining with
          ⟨candidate, member, equal⟩
        exact ⟨candidate, List.mem_cons_of_mem current member, equal⟩

private theorem payloadPresent_insertWeighted_of_present {α : Type}
    [DecidableEq α] (item : α) (inserted : Weighted α) :
    ∀ atoms : List (Weighted α),
      PayloadPresent item atoms →
        PayloadPresent item (insertWeighted inserted atoms)
  | [], present => by
      rcases present with ⟨atom, member, equal⟩
      cases member
  | current :: remaining, present => by
      rcases present with ⟨candidate, member, equal⟩
      rcases List.mem_cons.mp member with head | tail
      · subst candidate
        by_cases same : inserted.item = current.item
        · simp only [insertWeighted, same, ↓reduceDIte]
          exact ⟨_, List.mem_cons_self, equal⟩
        · simp only [insertWeighted, same, ↓reduceDIte]
          exact ⟨current, List.mem_cons_self, equal⟩
      · by_cases same : inserted.item = current.item
        · simp only [insertWeighted, same, ↓reduceDIte]
          exact ⟨candidate, List.mem_cons_of_mem _ tail, equal⟩
        · simp only [insertWeighted, same, ↓reduceDIte]
          rcases payloadPresent_insertWeighted_of_present item inserted
              remaining ⟨candidate, tail, equal⟩ with
            ⟨found, foundMember, foundEqual⟩
          exact ⟨found, List.mem_cons_of_mem current foundMember, foundEqual⟩

private theorem payloadPresent_consolidateAtoms_of_mem {α : Type}
    [DecidableEq α] :
    ∀ (atoms : List (Weighted α)) (atom : Weighted α),
      atom ∈ atoms → PayloadPresent atom.item (consolidateAtoms atoms)
  | [], atom, member => by cases member
  | head :: remaining, atom, member => by
      rw [consolidateAtoms]
      rcases List.mem_cons.mp member with same | tail
      · subst atom
        exact payloadPresent_insertWeighted_self head
          (consolidateAtoms remaining)
      · exact payloadPresent_insertWeighted_of_present atom.item head
          (consolidateAtoms remaining)
          (payloadPresent_consolidateAtoms_of_mem remaining atom tail)

private theorem payloadAbsent_ne_of_mem {α : Type} (item : α) :
    ∀ {atoms : List (Weighted α)}, PayloadAbsent item atoms →
      ∀ {atom : Weighted α}, atom ∈ atoms → item ≠ atom.item
  | [], absent, atom, member => by cases member
  | head :: remaining, absent, atom, member => by
      rcases absent with ⟨headDifferent, tailAbsent⟩
      rcases List.mem_cons.mp member with same | tail
      · subst atom
        exact headDifferent
      · exact payloadAbsent_ne_of_mem item tailAbsent tail

private theorem payloadPresent_tail_of_cons_of_ne {α : Type}
    (item : α) (head : Weighted α) (remaining : List (Weighted α))
    (different : item ≠ head.item)
    (present : PayloadPresent item (head :: remaining)) :
    PayloadPresent item remaining := by
  rcases present with ⟨candidate, member, equal⟩
  rcases List.mem_cons.mp member with same | tail
  · subst candidate
    exact (different equal.symm).elim
  · exact ⟨candidate, tail, equal⟩

private theorem mem_restrictAtoms_original {α : Type}
    (event : α → Bool) :
    ∀ {atoms : List (Weighted α)} {atom : Weighted α},
      atom ∈ restrictAtoms atoms event → atom ∈ atoms
  | [], atom, member => by cases member
  | head :: remaining, atom, member => by
      cases selected : event head.item
      · simp only [restrictAtoms, selected] at member
        exact List.mem_cons_of_mem head
          (mem_restrictAtoms_original event member)
      · simp only [restrictAtoms, selected] at member
        rcases List.mem_cons.mp member with same | tail
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem head
            (mem_restrictAtoms_original event tail)

private theorem mem_restrictAtoms_selected {α : Type}
    (event : α → Bool) :
    ∀ {atoms : List (Weighted α)} {atom : Weighted α},
      atom ∈ restrictAtoms atoms event → event atom.item = true
  | [], atom, member => by cases member
  | head :: remaining, atom, member => by
      cases selected : event head.item
      · simp only [restrictAtoms, selected] at member
        exact mem_restrictAtoms_selected event member
      · simp only [restrictAtoms, selected] at member
        rcases List.mem_cons.mp member with same | tail
        · subst atom
          exact selected
        · exact mem_restrictAtoms_selected event tail

namespace FiniteContent

/-- A duplicate-free key list covers a content when every displayed content
atom has a key with the same payload. -/
def PayloadsCovered {α : Type} (content : FiniteContent α)
    (keys : List (Weighted α)) : Prop :=
  ∀ atom, atom ∈ content.atoms → PayloadPresent atom.item keys

/-- Sum exact singleton masses once for every displayed key. -/
def atomMassSum {α : Type} [DecidableEq α]
    (content : FiniteContent α) :
    List (Weighted α) → (α → Coordinate) → Coordinate
  | [], _ => 0
  | key :: remaining, value =>
      content.measure (atomEvent key.item) * value key.item +
        content.atomMassSum remaining value

/-- Singleton-mass sums agree when the two contents assign the same mass to
every displayed key payload. -/
theorem atomMassSum_congr {α : Type} [DecidableEq α]
    (left right : FiniteContent α) (value : α → Coordinate) :
    ∀ keys : List (Weighted α),
      (∀ key, key ∈ keys →
        left.measure (atomEvent key.item) =
          right.measure (atomEvent key.item)) →
      left.atomMassSum keys value = right.atomMassSum keys value
  | [], equal => rfl
  | key :: remaining, equal => by
      simp only [atomMassSum]
      rw [equal key List.mem_cons_self,
        atomMassSum_congr left right value remaining
          (fun candidate member =>
            equal candidate (List.mem_cons_of_mem key member))]

private theorem restrict_singleton_integral {α : Type} [DecidableEq α]
    (content : FiniteContent α) (item : α)
    (value : α → Coordinate) :
    (content.restrict (atomEvent item)).integral value =
      content.measure (atomEvent item) * value item := by
  rw [content.restrict_integral]
  calc
    content.integral (fun candidate =>
          Distribution.indicator (atomEvent item) candidate *
            value candidate) =
        content.integral (fun candidate =>
          value item * Distribution.indicator (atomEvent item) candidate) :=
      content.integral_congr _ _ (fun candidate => by
        cases selected : atomEvent item candidate
        · simp only [Distribution.indicator, selected, mul_zero, zero_mul]
        · have same : candidate = item := by
            unfold atomEvent at selected
            exact of_decide_eq_true selected
          rw [same]
          ring1)
    _ = value item *
          content.integral (Distribution.indicator (atomEvent item)) :=
      content.integral_scale _ _
    _ = value item * content.measure (atomEvent item) :=
      congrArg (fun mass => value item * mass)
        (content.integral_indicator (atomEvent item))
    _ = content.measure (atomEvent item) * value item := by ring1

private theorem restrict_add_complement_integral {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (value : α → Coordinate) :
    (content.restrict event).integral value +
        (content.restrict (complementEvent event)).integral value =
      content.integral value := by
  rw [content.restrict_integral, content.restrict_integral]
  calc
    content.integral (fun item =>
          Distribution.indicator event item * value item) +
        content.integral (fun item =>
          Distribution.indicator (complementEvent event) item * value item) =
      content.integral (fun item =>
        Distribution.indicator event item * value item +
          Distribution.indicator (complementEvent event) item * value item) :=
      (content.integral_add _ _).symm
    _ = content.integral value :=
      content.integral_congr _ _ (fun item => by
        cases selected : event item <;>
          simp only [Distribution.indicator, complementEvent, selected,
            Bool.not_false, Bool.not_true, zero_mul, one_mul,
            add_zero, zero_add])

private theorem restrict_complement_singleton_mass {α : Type}
    [DecidableEq α] (content : FiniteContent α)
    (removed kept : α) (different : kept ≠ removed) :
    (content.restrict (complementEvent (atomEvent removed))).measure
        (atomEvent kept) = content.measure (atomEvent kept) := by
  rw [content.restrict_measure]
  exact content.measure_congr _ _ (fun candidate => by
    cases selected : atomEvent kept candidate
    · simp only [intersectionEvent, selected, Bool.false_and]
    · have same : candidate = kept := by
        unfold atomEvent at selected
        exact of_decide_eq_true selected
      have notRemoved : atomEvent removed candidate = false := by
        unfold atomEvent
        rw [same]
        simp only [decide_eq_false_iff_not]
        exact different
      simp only [intersectionEvent, complementEvent, selected, notRemoved,
        Bool.not_false, Bool.and_true])

/-- Histogram reconstruction: singleton masses over a duplicate-free key
list covering the displayed table recover every exact rational integral. -/
theorem atomMassSum_eq_integral {α : Type} [DecidableEq α]
    (value : α → Coordinate) :
    ∀ (keys : List (Weighted α)) (content : FiniteContent α),
      NoRepeatedPayloads keys → content.PayloadsCovered keys →
        content.atomMassSum keys value = content.integral value
  | [], content, noRepeated, covered => by
      cases atomsSame : content.atoms with
      | nil =>
          simp only [atomMassSum, FiniteContent.integral, atomsSame,
            Distribution.expectationWeight]
      | cons atom remaining =>
          have present := covered atom (atomsSame ▸ List.mem_cons_self)
          rcases present with ⟨candidate, member, equal⟩
          cases member
  | key :: remaining, content, noRepeated, covered => by
      rcases noRepeated with ⟨keyAbsent, tailNoRepeated⟩
      let residual :=
        content.restrict (complementEvent (atomEvent key.item))
      have residualCovered : residual.PayloadsCovered remaining := by
        intro atom member
        have originalMember : atom ∈ content.atoms :=
          mem_restrictAtoms_original
            (complementEvent (atomEvent key.item)) member
        have complementSelected :
            complementEvent (atomEvent key.item) atom.item = true :=
          mem_restrictAtoms_selected
            (complementEvent (atomEvent key.item)) member
        have different : atom.item ≠ key.item := by
          intro same
          have selectedSelf : atomEvent key.item atom.item = true := by
            unfold atomEvent
            simp only [same, decide_true]
          unfold complementEvent at complementSelected
          rw [selectedSelf] at complementSelected
          exact Bool.noConfusion complementSelected
        exact payloadPresent_tail_of_cons_of_ne atom.item key remaining
          different (covered atom originalMember)
      have tailMassEqual : content.atomMassSum remaining value =
          residual.atomMassSum remaining value := by
        apply atomMassSum_congr content residual value remaining
        intro candidate member
        have different : candidate.item ≠ key.item := by
          intro same
          exact (payloadAbsent_ne_of_mem key.item keyAbsent member) same.symm
        exact (restrict_complement_singleton_mass content key.item
          candidate.item different).symm
      calc
        content.atomMassSum (key :: remaining) value =
            content.measure (atomEvent key.item) * value key.item +
              content.atomMassSum remaining value := rfl
        _ = (content.restrict (atomEvent key.item)).integral value +
              residual.atomMassSum remaining value := by
          rw [restrict_singleton_integral, tailMassEqual]
        _ = (content.restrict (atomEvent key.item)).integral value +
              residual.integral value := by
          rw [atomMassSum_eq_integral value remaining residual
            tailNoRepeated residualCovered]
        _ = content.integral value :=
          restrict_add_complement_integral content (atomEvent key.item) value

/-- Build one content row per key, weighted by the original singleton mass. -/
def atomMassContent {α : Type} [DecidableEq α]
    (content : FiniteContent α) (keys : List (Weighted α)) :
    FiniteContent α where
  atoms := keys.map fun key =>
    { item := key.item
      weight := content.measure (atomEvent key.item)
      nonnegative := content.measure_nonneg (atomEvent key.item) }

theorem atomMassContent_integral {α : Type} [DecidableEq α]
    (content : FiniteContent α) (keys : List (Weighted α))
    (value : α → Coordinate) :
    (content.atomMassContent keys).integral value =
      content.atomMassSum keys value := by
  unfold atomMassContent FiniteContent.integral
  induction keys with
  | nil => rfl
  | cons key remaining inductionHypothesis =>
      simp only [List.map_cons, Distribution.expectationWeight, atomMassSum,
        inductionHypothesis]

theorem atomMassContent_evaluationEquivalent {α : Type} [DecidableEq α]
    (content : FiniteContent α) (keys : List (Weighted α))
    (noRepeated : NoRepeatedPayloads keys)
    (covered : content.PayloadsCovered keys) :
    EvaluationEquivalent (content.atomMassContent keys) content := by
  apply EvaluationEquivalent.of_integral_eq
  intro value
  rw [content.atomMassContent_integral keys value]
  exact content.atomMassSum_eq_integral value keys noRepeated covered

/-- Duplicate-free union of the source and target payload catalogues. -/
def radonNikodymKeys {α : Type} [DecidableEq α]
    (source target : FiniteContent α) : List (Weighted α) :=
  consolidateAtoms (source.atoms ++ target.atoms)

theorem radonNikodymKeys_noRepeated {α : Type} [DecidableEq α]
    (source target : FiniteContent α) :
    NoRepeatedPayloads (source.radonNikodymKeys target) :=
  consolidateAtoms_noRepeatedPayloads _

theorem payloadsCovered_radonNikodymKeys_left {α : Type}
    [DecidableEq α] (source target : FiniteContent α) :
    source.PayloadsCovered (source.radonNikodymKeys target) := by
  intro atom member
  exact payloadPresent_consolidateAtoms_of_mem
    (source.atoms ++ target.atoms) atom
    (List.mem_append_left target.atoms member)

theorem payloadsCovered_radonNikodymKeys_right {α : Type}
    [DecidableEq α] (source target : FiniteContent α) :
    target.PayloadsCovered (source.radonNikodymKeys target) := by
  intro atom member
  exact payloadPresent_consolidateAtoms_of_mem
    (source.atoms ++ target.atoms) atom
    (List.mem_append_right source.atoms member)

namespace EvaluationEquivalent

/-- Agreement on every executable singleton event determines all finite
event measures and rational integrals. -/
theorem of_atom_measure_eq {α : Type} [DecidableEq α]
    {left right : FiniteContent α}
    (atomEqual : ∀ item : α,
      left.measure (atomEvent item) = right.measure (atomEvent item)) :
    EvaluationEquivalent left right := by
  apply EvaluationEquivalent.of_integral_eq
  intro value
  let keys := left.radonNikodymKeys right
  calc
    left.integral value = left.atomMassSum keys value :=
      (left.atomMassSum_eq_integral value keys
        (left.radonNikodymKeys_noRepeated right)
        (left.payloadsCovered_radonNikodymKeys_left right)).symm
    _ = right.atomMassSum keys value := by
      apply atomMassSum_congr left right value keys
      intro key member
      exact atomEqual key.item
    _ = right.integral value :=
      right.atomMassSum_eq_integral value keys
        (left.radonNikodymKeys_noRepeated right)
        (left.payloadsCovered_radonNikodymKeys_right right)

/-- Observationally equivalent finite contents agree on every singleton
mass. -/
theorem atom_measure_eq {α : Type} [DecidableEq α]
    {left right : FiniteContent α}
    (equivalent : EvaluationEquivalent left right) (item : α) :
    left.measure (atomEvent item) = right.measure (atomEvent item) :=
  equivalent.measure_eq (atomEvent item)

end EvaluationEquivalent

/-- Finite contents are observationally equivalent exactly when their
singleton rational masses agree pointwise. -/
theorem evaluationEquivalent_iff_atom_measure_eq {α : Type}
    [DecidableEq α] (left right : FiniteContent α) :
    EvaluationEquivalent left right ↔
      ∀ item : α,
        left.measure (atomEvent item) = right.measure (atomEvent item) :=
  ⟨fun equivalent item => equivalent.atom_measure_eq item,
    EvaluationEquivalent.of_atom_measure_eq⟩

end FiniteContent

private theorem atomicRowPayloadAbsent_map_atomMass {α : Type}
    [DecidableEq α] (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source)
    (item : α) :
    ∀ keys : List (Weighted α), PayloadAbsent item keys →
      AtomicRowPayloadAbsent item
        (keys.map fun key =>
          { item := key.item
            sourceWeight := source.measure (atomEvent key.item)
            targetWeight := target.measure (atomEvent key.item)
            source_nonnegative := source.measure_nonneg _
            target_nonnegative := target.measure_nonneg _
            target_zero_of_source_zero := fun zero =>
              continuous (atomEvent key.item) zero :
              AtomicChangeRow α })
  | [], absent => trivial
  | key :: remaining, absent => by
      rcases absent with ⟨head, tail⟩
      simp only [List.map_cons, AtomicRowPayloadAbsent]
      exact ⟨head, atomicRowPayloadAbsent_map_atomMass source target
        continuous item remaining tail⟩

private theorem noRepeatedAtomicRows_map_atomMass {α : Type}
    [DecidableEq α] (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source) :
    ∀ keys : List (Weighted α), NoRepeatedPayloads keys →
      NoRepeatedAtomicRows
        (keys.map fun key =>
          { item := key.item
            sourceWeight := source.measure (atomEvent key.item)
            targetWeight := target.measure (atomEvent key.item)
            source_nonnegative := source.measure_nonneg _
            target_nonnegative := target.measure_nonneg _
            target_zero_of_source_zero := fun zero =>
              continuous (atomEvent key.item) zero :
              AtomicChangeRow α })
  | [], noRepeated => trivial
  | key :: remaining, noRepeated => by
      rcases noRepeated with ⟨headAbsent, tailNoRepeated⟩
      simp only [List.map_cons, NoRepeatedAtomicRows]
      exact ⟨atomicRowPayloadAbsent_map_atomMass source target continuous
          key.item remaining headAbsent,
        noRepeatedAtomicRows_map_atomMass source target continuous remaining
          tailNoRepeated⟩

private theorem expectationWeight_sourceAtoms_map_atomMass {α : Type}
    [DecidableEq α] (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source)
    (value : α → Coordinate) :
    ∀ keys : List (Weighted α),
      Distribution.expectationWeight
          (AtomicChange.sourceAtoms
            (keys.map fun key =>
              { item := key.item
                sourceWeight := source.measure (atomEvent key.item)
                targetWeight := target.measure (atomEvent key.item)
                source_nonnegative := source.measure_nonneg _
                target_nonnegative := target.measure_nonneg _
                target_zero_of_source_zero := fun zero =>
                  continuous (atomEvent key.item) zero :
                  AtomicChangeRow α }))
          value = source.atomMassSum keys value
  | [] => rfl
  | key :: remaining => by
      simp only [List.map_cons, AtomicChange.sourceAtoms,
        Distribution.expectationWeight, FiniteContent.atomMassSum,
        expectationWeight_sourceAtoms_map_atomMass source target continuous
          value remaining]

private theorem expectationWeight_targetAtoms_map_atomMass {α : Type}
    [DecidableEq α] (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source)
    (value : α → Coordinate) :
    ∀ keys : List (Weighted α),
      Distribution.expectationWeight
          (AtomicChange.targetAtoms
            (keys.map fun key =>
              { item := key.item
                sourceWeight := source.measure (atomEvent key.item)
                targetWeight := target.measure (atomEvent key.item)
                source_nonnegative := source.measure_nonneg _
                target_nonnegative := target.measure_nonneg _
                target_zero_of_source_zero := fun zero =>
                  continuous (atomEvent key.item) zero :
                  AtomicChangeRow α }))
          value = target.atomMassSum keys value
  | [] => rfl
  | key :: remaining => by
      simp only [List.map_cons, AtomicChange.targetAtoms,
        Distribution.expectationWeight, FiniteContent.atomMassSum,
        expectationWeight_targetAtoms_map_atomMass source target continuous
          value remaining]

namespace AtomicChange

/-- Aligned singleton-mass rows for arbitrary absolutely continuous finite
contents. -/
def ofAbsolutelyContinuous {α : Type} [DecidableEq α]
    (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source) : AtomicChange α where
  rows := (source.radonNikodymKeys target).map fun key =>
    { item := key.item
      sourceWeight := source.measure (atomEvent key.item)
      targetWeight := target.measure (atomEvent key.item)
      source_nonnegative := source.measure_nonneg _
      target_nonnegative := target.measure_nonneg _
      target_zero_of_source_zero := fun zero =>
        continuous (atomEvent key.item) zero }
  noRepeated := by
    exact noRepeatedAtomicRows_map_atomMass source target continuous
      (source.radonNikodymKeys target)
      (source.radonNikodymKeys_noRepeated target)

theorem ofAbsolutelyContinuous_source_evaluationEquivalent {α : Type}
    [DecidableEq α] (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source) :
    FiniteContent.EvaluationEquivalent
      (ofAbsolutelyContinuous source target continuous).source source := by
  apply FiniteContent.EvaluationEquivalent.of_integral_eq
  intro value
  unfold AtomicChange.source ofAbsolutelyContinuous FiniteContent.integral
  rw [expectationWeight_sourceAtoms_map_atomMass source target continuous
    value]
  exact source.atomMassSum_eq_integral value
    (source.radonNikodymKeys target)
    (source.radonNikodymKeys_noRepeated target)
    (source.payloadsCovered_radonNikodymKeys_left target)

theorem ofAbsolutelyContinuous_target_evaluationEquivalent {α : Type}
    [DecidableEq α] (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source) :
    FiniteContent.EvaluationEquivalent
      (ofAbsolutelyContinuous source target continuous).target target := by
  apply FiniteContent.EvaluationEquivalent.of_integral_eq
  intro value
  unfold AtomicChange.target ofAbsolutelyContinuous FiniteContent.integral
  rw [expectationWeight_targetAtoms_map_atomMass source target continuous
    value]
  exact target.atomMassSum_eq_integral value
    (source.radonNikodymKeys target)
    (source.radonNikodymKeys_noRepeated target)
    (source.payloadsCovered_radonNikodymKeys_right target)

namespace Witness

/-- Transport a density witness across observationally equivalent source and
target table layouts. -/
def transport {α : Type}
    {alignedSource alignedTarget source target : FiniteContent α}
    (witness : Witness alignedSource alignedTarget)
    (sourceEquivalent : FiniteContent.EvaluationEquivalent
      alignedSource source)
    (targetEquivalent : FiniteContent.EvaluationEquivalent
      alignedTarget target) : Witness source target where
  density := witness.density
  nonnegative := witness.nonnegative
  integral_eq value := by
    calc
      target.integral value = alignedTarget.integral value :=
        (targetEquivalent.integral_eq value).symm
      _ = alignedSource.integral (fun item =>
          witness.density item * value item) := witness.integral_eq value
      _ = source.integral (fun item =>
          witness.density item * value item) :=
        sourceEquivalent.integral_eq _

/-- Every absolutely continuous pair of displayed finite contents has an
explicit rational Radon--Nikodym density. -/
def ofAbsolutelyContinuous {α : Type} [DecidableEq α]
    (source target : FiniteContent α)
    (continuous : target.AbsolutelyContinuous source) :
    Witness source target :=
  let change := AtomicChange.ofAbsolutelyContinuous source target continuous
  change.witness.transport
    (AtomicChange.ofAbsolutelyContinuous_source_evaluationEquivalent
      source target continuous)
    (AtomicChange.ofAbsolutelyContinuous_target_evaluationEquivalent
      source target continuous)

end Witness

end AtomicChange

end FiniteMeasure
