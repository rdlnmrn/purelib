import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConditionalProjection
import FiniteMeasure.AlmostEverywhere

/-!
# Characterization and uniqueness of finite conditional expectation

An explicitly cellwise observable is the conditional expectation of a
rational observable exactly when it preserves the restricted integral on
every displayed partition cell.  Positivity of each cell permits direct
rational cancellation, giving equality on every displayed atom and hence
the usual almost-everywhere and L1 uniqueness consequences.
-/

namespace FiniteMeasure

namespace PositiveEventPartition

private theorem exists_selected_event_of_unionEvents_eq_true {α : Type}
    (item : α) :
    ∀ (events : List (α → Bool)), unionEvents events item = true →
      ∃ event, event ∈ events ∧ event item = true
  | [], covered => by
      simp only [unionEvents] at covered
      exact Bool.noConfusion covered
  | event :: remaining, covered => by
      cases selected : event item
      · have tailCovered : unionEvents remaining item = true := by
          simpa only [unionEvents, unionEvent, selected, Bool.false_or]
            using covered
        rcases exists_selected_event_of_unionEvents_eq_true item remaining
          tailCovered with ⟨target, member, targetSelected⟩
        exact ⟨target, List.mem_cons_of_mem event member, targetSelected⟩
      · exact ⟨event, List.mem_cons_self, selected⟩

/-- The restricted integral of a cellwise observable is its displayed cell
value multiplied by the cell probability. -/
theorem eventIntegral_cellwise {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (candidate : α → Coordinate)
    (represented : CellwiseObservable partition candidate)
    (event : α → Bool) (eventMember : event ∈ partition.events) :
    distribution.eventIntegral event candidate =
      distribution.probability event * represented.cellValue event := by
  calc
    distribution.eventIntegral event candidate =
        distribution.eventIntegral event
          (fun _ => represented.cellValue event) := by
      unfold Distribution.eventIntegral
      apply distribution.expectation_congr_off_zero
      intro atom atomMember
      apply Or.inr
      cases selected : event atom.item
      · simp only [Distribution.indicator, selected, zero_mul]
      · simp only [Distribution.indicator, selected, one_mul]
        exact represented.agrees event eventMember atom atomMember selected
    _ = distribution.probability event * represented.cellValue event :=
      distribution.eventIntegral_constant event (represented.cellValue event)

/-- On a positive cell, the conditional mean of a cellwise observable is
its explicit cell value. -/
theorem conditionalMean_cellwise {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (candidate : α → Coordinate)
    (represented : CellwiseObservable partition candidate)
    (event : α → Bool) (eventMember : event ∈ partition.events) :
    distribution.conditionalMean event candidate =
      represented.cellValue event := by
  let probability := distribution.probability event
  have positive : 0 < probability := partition.positive event eventMember
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne positive.ne'
  calc
    distribution.conditionalMean event candidate * probability =
        probability * distribution.conditionalMean event candidate := by
      ring1
    _ = distribution.eventIntegral event candidate :=
      distribution.probability_mul_conditionalMean event candidate positive
    _ = probability * represented.cellValue event :=
      partition.eventIntegral_cellwise candidate represented event eventMember
    _ = represented.cellValue event * probability := by ring1

/-- Cellwise restricted-integral preservation characterizes conditional
expectation pointwise on every displayed atom. -/
theorem candidate_eq_conditionalExpectation_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value candidate : α → Coordinate)
    (represented : CellwiseObservable partition candidate)
    (preserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event candidate =
        distribution.eventIntegral event value) :
    ∀ atom, atom ∈ distribution.atoms →
      candidate atom.item = partition.conditionalExpectation value atom.item := by
  intro atom atomMember
  have covered := partition.covers atom atomMember
  rcases exists_selected_event_of_unionEvents_eq_true atom.item
    partition.events covered with ⟨event, eventMember, selected⟩
  have meansEqual : distribution.conditionalMean event candidate =
      distribution.conditionalMean event value := by
    unfold Distribution.conditionalMean
    rw [preserves event eventMember]
  calc
    candidate atom.item = represented.cellValue event :=
      represented.agrees event eventMember atom atomMember selected
    _ = distribution.conditionalMean event candidate :=
      (partition.conditionalMean_cellwise candidate represented event
        eventMember).symm
    _ = distribution.conditionalMean event value := meansEqual
    _ = partition.conditionalExpectation value atom.item :=
      (partition.conditionalExpectation_eq_conditionalMean_on_cell
        value event eventMember atom atomMember selected).symm

/-- The characterization gives the standard almost-everywhere uniqueness
statement immediately. -/
theorem candidate_equalAlmostEverywhere_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value candidate : α → Coordinate)
    (represented : CellwiseObservable partition candidate)
    (preserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event candidate =
        distribution.eventIntegral event value) :
    distribution.EqualAlmostEverywhere candidate
      (partition.conditionalExpectation value) := by
  intro atom atomMember
  exact Or.inr (partition.candidate_eq_conditionalExpectation_on_atoms
    value candidate represented preserves atom atomMember)

/-- Equivalently, every characterized candidate has zero exact finite L1
distance from conditional expectation. -/
theorem l1Distance_candidate_conditionalExpectation_eq_zero {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value candidate : α → Coordinate)
    (represented : CellwiseObservable partition candidate)
    (preserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event candidate =
        distribution.eventIntegral event value) :
    distribution.l1Distance candidate
        (partition.conditionalExpectation value) = 0 :=
  (distribution.l1Distance_eq_zero_iff candidate
    (partition.conditionalExpectation value)).2
      (partition.candidate_equalAlmostEverywhere_conditionalExpectation
        value candidate represented preserves)

/-- Two cellwise observables preserving the same cell integrals agree on
every displayed atom. -/
theorem characterized_candidates_eq_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value left right : α → Coordinate)
    (leftCellwise : CellwiseObservable partition left)
    (rightCellwise : CellwiseObservable partition right)
    (leftPreserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event left =
        distribution.eventIntegral event value)
    (rightPreserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event right =
        distribution.eventIntegral event value) :
    ∀ atom, atom ∈ distribution.atoms → left atom.item = right atom.item := by
  intro atom atomMember
  rw [partition.candidate_eq_conditionalExpectation_on_atoms
      value left leftCellwise leftPreserves atom atomMember,
    partition.candidate_eq_conditionalExpectation_on_atoms
      value right rightCellwise rightPreserves atom atomMember]

end PositiveEventPartition

end FiniteMeasure
