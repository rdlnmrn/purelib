import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Probability

/-!
# Shared finite weighted-list operations

These scaling and append identities are the list-algebra layer shared by
finite contents and normalized finite distributions.
-/

namespace FiniteMeasure

open Distribution

/-- Multiply every displayed atom weight by a nonnegative rational factor. -/
def scaleAtoms {α : Type} (factor : Coordinate) (nonnegative : 0 ≤ factor) :
    List (Weighted α) → List (Weighted α)
  | [] => []
  | atom :: remaining =>
      { item := atom.item
        weight := factor * atom.weight
        nonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
          nonnegative atom.nonnegative } ::
        scaleAtoms factor nonnegative remaining

theorem scaleAtoms_length {α : Type}
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) :
    (scaleAtoms factor nonnegative atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [scaleAtoms, List.length_cons, inductionHypothesis]

/-- Every row of a scaled atom table retains the payload of an explicitly
displayed source row. -/
theorem mem_scaleAtoms_source {α : Type}
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (candidate : Weighted α) :
    ∀ {atoms : List (Weighted α)},
      candidate ∈ scaleAtoms factor nonnegative atoms →
        ∃ source, source ∈ atoms ∧ source.item = candidate.item
  | [], member => (List.not_mem_nil member).elim
  | atom :: remaining, member => by
      simp only [scaleAtoms, List.mem_cons] at member
      rcases member with equal | tailMember
      · refine ⟨atom, List.mem_cons_self, ?_⟩
        have itemEqual := congrArg (fun row : Weighted α => row.item) equal
        exact itemEqual.symm
      · rcases mem_scaleAtoms_source factor nonnegative candidate tailMember
          with ⟨source, sourceMember, itemEqual⟩
        exact ⟨source, List.mem_cons_of_mem atom sourceMember, itemEqual⟩

theorem totalWeight_scaleAtoms {α : Type}
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) :
    totalWeight (scaleAtoms factor nonnegative atoms) =
      factor * totalWeight atoms := by
  induction atoms with
  | nil =>
      simp only [scaleAtoms, totalWeight, mul_zero]
  | cons atom remaining inductionHypothesis =>
      simp only [scaleAtoms, totalWeight, inductionHypothesis]
      ring1

theorem eventWeight_append {α : Type} (left right : List (Weighted α))
    (event : α → Bool) :
    eventWeight (left ++ right) event =
      eventWeight left event + eventWeight right event := by
  induction left with
  | nil =>
      simp only [List.nil_append, eventWeight, zero_add]
  | cons atom remaining inductionHypothesis =>
      simp only [List.cons_append, eventWeight, inductionHypothesis]
      ring1

theorem expectationWeight_append {α : Type}
    (left right : List (Weighted α)) (value : α → Coordinate) :
    expectationWeight (left ++ right) value =
      expectationWeight left value + expectationWeight right value := by
  induction left with
  | nil =>
      simp only [List.nil_append, expectationWeight, zero_add]
  | cons atom remaining inductionHypothesis =>
      simp only [List.cons_append, expectationWeight, inductionHypothesis]
      ring1

/-- Scaling a finite atom list scales every executable event exactly. -/
theorem eventWeight_scaleAtoms {α : Type}
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) (event : α → Bool) :
    eventWeight (scaleAtoms factor nonnegative atoms) event =
      factor * eventWeight atoms event := by
  induction atoms with
  | nil =>
      simp only [scaleAtoms, eventWeight, mul_zero]
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item <;>
        simp only [scaleAtoms, eventWeight, selected, inductionHypothesis] <;>
        ring1

/-- Scaling a finite atom list scales every rational evaluation exactly. -/
theorem expectationWeight_scaleAtoms {α : Type}
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) (value : α → Coordinate) :
    expectationWeight (scaleAtoms factor nonnegative atoms) value =
      factor * expectationWeight atoms value := by
  induction atoms with
  | nil =>
      simp only [scaleAtoms, expectationWeight, mul_zero]
  | cons atom remaining inductionHypothesis =>
      simp only [scaleAtoms, expectationWeight, inductionHypothesis]
      ring1

end FiniteMeasure
