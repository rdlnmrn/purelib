import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.DistributionEquivalence

/-!
# Constructive consolidation of finite atom tables

When equality of payloads is explicitly decidable, repeated payloads can be
merged by finite recursion and rational weight addition.  This is an
executable histogram operation; no quotient or choice of representatives is
used.
-/

namespace FiniteMeasure

/-- Executable singleton event from a supplied decidable equality. -/
def atomEvent {α : Type} [DecidableEq α] (target candidate : α) : Bool :=
  decide (candidate = target)

/-- Insert one weighted atom, adding its rational weight to the first equal
payload already displayed. -/
def insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) : List (Weighted α) → List (Weighted α)
  | [] => [atom]
  | current :: remaining =>
      if _ : atom.item = current.item then
        { item := current.item
          weight := atom.weight + current.weight
          nonnegative := add_nonneg atom.nonnegative current.nonnegative } ::
            remaining
      else
        current :: insertWeighted atom remaining

theorem totalWeight_insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) : ∀ atoms : List (Weighted α),
    totalWeight (insertWeighted atom atoms) =
      atom.weight + totalWeight atoms
  | [] => by
      simp only [insertWeighted, totalWeight, add_zero]
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · simp only [insertWeighted, equal, ↓reduceDIte, totalWeight]
        ring1
      · simp only [insertWeighted, equal, ↓reduceDIte, totalWeight,
          totalWeight_insertWeighted atom remaining]
        ring1

theorem eventWeight_insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) (event : α → Bool) :
    ∀ atoms : List (Weighted α),
    eventWeight (insertWeighted atom atoms) event =
      (match event atom.item with
        | true => atom.weight
        | false => 0) + eventWeight atoms event
  | [] => by
      cases selected : event atom.item <;>
        simp only [insertWeighted, eventWeight, selected, add_zero]
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · cases selected : event current.item
        · simp only [insertWeighted, equal, ↓reduceDIte, eventWeight,
            selected, zero_add]
        · simp only [insertWeighted, equal, ↓reduceDIte, eventWeight,
            selected]
          ring1
      · cases atomSelected : event atom.item <;>
          cases currentSelected : event current.item <;>
          simp only [insertWeighted, equal, ↓reduceDIte, eventWeight,
            atomSelected, currentSelected,
            eventWeight_insertWeighted atom event remaining]
        all_goals ring1

theorem expectationWeight_insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) (value : α → Coordinate) :
    ∀ atoms : List (Weighted α),
    Distribution.expectationWeight (insertWeighted atom atoms) value =
      atom.weight * value atom.item +
        Distribution.expectationWeight atoms value
  | [] => by
      simp only [insertWeighted, Distribution.expectationWeight, add_zero]
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · simp only [insertWeighted, equal, ↓reduceDIte,
          Distribution.expectationWeight]
        ring1
      · simp only [insertWeighted, equal, ↓reduceDIte,
          Distribution.expectationWeight,
          expectationWeight_insertWeighted atom value remaining]
        ring1

theorem insertWeighted_length_le {α : Type} [DecidableEq α]
    (atom : Weighted α) : ∀ atoms : List (Weighted α),
    (insertWeighted atom atoms).length ≤ atoms.length + 1
  | [] => le_rfl
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · simp only [insertWeighted, equal, ↓reduceDIte, List.length_cons]
        exact Nat.le_add_right _ 1
      · simp only [insertWeighted, equal, ↓reduceDIte, List.length_cons]
        exact Nat.succ_le_succ (insertWeighted_length_le atom remaining)

/-- A displayed payload is absent from a finite weighted table. -/
def PayloadAbsent {α : Type} (item : α) : List (Weighted α) → Prop
  | [] => True
  | atom :: remaining =>
      item ≠ atom.item ∧ PayloadAbsent item remaining

/-- No payload occurs twice in a displayed weighted table. -/
def NoRepeatedPayloads {α : Type} : List (Weighted α) → Prop
  | [] => True
  | atom :: remaining =>
      PayloadAbsent atom.item remaining ∧ NoRepeatedPayloads remaining

theorem payloadAbsent_insertWeighted {α : Type} [DecidableEq α]
    (item : α) (atom : Weighted α) (different : item ≠ atom.item) :
    ∀ atoms : List (Weighted α), PayloadAbsent item atoms →
      PayloadAbsent item (insertWeighted atom atoms)
  | [], absent => by
      simp only [insertWeighted, PayloadAbsent]
      exact ⟨different, trivial⟩
  | current :: remaining, absent => by
      rcases absent with ⟨currentDifferent, remainingAbsent⟩
      by_cases equal : atom.item = current.item
      · simp only [insertWeighted, equal, ↓reduceDIte, PayloadAbsent]
        exact ⟨currentDifferent, remainingAbsent⟩
      · simp only [insertWeighted, equal, ↓reduceDIte, PayloadAbsent]
        exact ⟨currentDifferent,
          payloadAbsent_insertWeighted item atom different remaining
            remainingAbsent⟩

theorem insertWeighted_noRepeatedPayloads {α : Type} [DecidableEq α]
    (atom : Weighted α) : ∀ atoms : List (Weighted α),
    NoRepeatedPayloads atoms →
      NoRepeatedPayloads (insertWeighted atom atoms)
  | [], noRepeated => by
      simp only [insertWeighted, NoRepeatedPayloads, PayloadAbsent]
      trivial
  | current :: remaining, noRepeated => by
      rcases noRepeated with ⟨currentAbsent, remainingNoRepeated⟩
      by_cases equal : atom.item = current.item
      · simp only [insertWeighted, equal, ↓reduceDIte, NoRepeatedPayloads]
        exact ⟨currentAbsent, remainingNoRepeated⟩
      · simp only [insertWeighted, equal, ↓reduceDIte, NoRepeatedPayloads]
        constructor
        · exact payloadAbsent_insertWeighted current.item atom
            (fun reverse => equal reverse.symm) remaining currentAbsent
        · exact insertWeighted_noRepeatedPayloads atom remaining
            remainingNoRepeated

/-- Merge all repeated payloads in a displayed finite weighted table. -/
def consolidateAtoms {α : Type} [DecidableEq α] :
    List (Weighted α) → List (Weighted α)
  | [] => []
  | atom :: remaining => insertWeighted atom (consolidateAtoms remaining)

theorem totalWeight_consolidateAtoms {α : Type} [DecidableEq α] :
    ∀ atoms : List (Weighted α),
      totalWeight (consolidateAtoms atoms) = totalWeight atoms
  | [] => rfl
  | atom :: remaining => by
      rw [consolidateAtoms, totalWeight_insertWeighted,
        totalWeight_consolidateAtoms remaining]
      rfl

theorem eventWeight_consolidateAtoms {α : Type} [DecidableEq α]
    (event : α → Bool) : ∀ atoms : List (Weighted α),
    eventWeight (consolidateAtoms atoms) event = eventWeight atoms event
  | [] => rfl
  | atom :: remaining => by
      rw [consolidateAtoms, eventWeight_insertWeighted,
        eventWeight_consolidateAtoms event remaining]
      rfl

theorem expectationWeight_consolidateAtoms {α : Type} [DecidableEq α]
    (value : α → Coordinate) : ∀ atoms : List (Weighted α),
    Distribution.expectationWeight (consolidateAtoms atoms) value =
      Distribution.expectationWeight atoms value
  | [] => rfl
  | atom :: remaining => by
      rw [consolidateAtoms, expectationWeight_insertWeighted,
        expectationWeight_consolidateAtoms value remaining]
      rfl

theorem consolidateAtoms_length_le {α : Type} [DecidableEq α] :
    ∀ atoms : List (Weighted α),
      (consolidateAtoms atoms).length ≤ atoms.length
  | [] => le_rfl
  | atom :: remaining => by
      rw [consolidateAtoms]
      exact (insertWeighted_length_le atom
        (consolidateAtoms remaining)).trans (by
          simpa only [List.length_cons, Nat.succ_eq_add_one] using
            Nat.add_le_add_right
              (consolidateAtoms_length_le remaining) 1)

/-- Consolidation really is a histogram: its displayed payloads are
pairwise unrepeated. -/
theorem consolidateAtoms_noRepeatedPayloads
    {α : Type} [DecidableEq α] :
    ∀ atoms : List (Weighted α),
      NoRepeatedPayloads (consolidateAtoms atoms)
  | [] => trivial
  | atom :: remaining => by
      rw [consolidateAtoms]
      exact insertWeighted_noRepeatedPayloads atom
        (consolidateAtoms remaining)
        (consolidateAtoms_noRepeatedPayloads remaining)

namespace Distribution

/-- Exact rational mass carried by all displayed rows equal to one supplied
payload. -/
def atomMass {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) : Coordinate :=
  source.probability (atomEvent item)

theorem atomMass_nonneg {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) :
    0 ≤ source.atomMass item :=
  source.probability_nonneg (atomEvent item)

theorem atomMass_le_one {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) :
    source.atomMass item ≤ 1 :=
  source.probability_le_one (atomEvent item)

/-- Executably merge repeated payloads in a finite rational distribution. -/
def consolidate {α : Type} [DecidableEq α]
    (source : Distribution α) : Distribution α where
  atoms := consolidateAtoms source.atoms
  total_one := by
    rw [totalWeight_consolidateAtoms, source.total_one]

theorem consolidate_atoms_length_le {α : Type} [DecidableEq α]
    (source : Distribution α) :
    source.consolidate.atoms.length ≤ source.atoms.length :=
  consolidateAtoms_length_le source.atoms

theorem consolidate_noRepeatedPayloads {α : Type} [DecidableEq α]
    (source : Distribution α) :
    NoRepeatedPayloads source.consolidate.atoms :=
  consolidateAtoms_noRepeatedPayloads source.atoms

/-- Consolidation preserves every exact finite event and observable
evaluation. -/
theorem consolidate_evaluationEquivalent {α : Type} [DecidableEq α]
    (source : Distribution α) :
    EvaluationEquivalent source.consolidate source where
  probability_eq event := eventWeight_consolidateAtoms event source.atoms
  expectation_eq value :=
    expectationWeight_consolidateAtoms value source.atoms

theorem consolidate_atomMass {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) :
    source.consolidate.atomMass item = source.atomMass item :=
  source.consolidate_evaluationEquivalent.probability_eq (atomEvent item)

/-- Consolidation respects evaluation equivalence of the input tables. -/
theorem EvaluationEquivalent.consolidate {α : Type} [DecidableEq α]
    {left right : Distribution α}
    (equivalent : EvaluationEquivalent left right) :
    EvaluationEquivalent left.consolidate right.consolidate :=
  (left.consolidate_evaluationEquivalent.trans equivalent).trans
    right.consolidate_evaluationEquivalent.symm

/-- Repeating consolidation changes no exact evaluation. -/
theorem consolidate_consolidate_evaluationEquivalent
    {α : Type} [DecidableEq α] (source : Distribution α) :
    EvaluationEquivalent source.consolidate.consolidate source.consolidate :=
  source.consolidate.consolidate_evaluationEquivalent

end Distribution

end FiniteMeasure
