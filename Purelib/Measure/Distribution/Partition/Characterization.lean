module
import Purelib.Measure.Distribution.Partition.Expectation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Measure.Event.Family
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Characterization and uniqueness of finite conditional expectation

An explicitly cellwise observable is the conditional expectation of a
rational observable exactly when it preserves the restricted integral on
every displayed partition cell.  Positivity of each cell permits direct
rational cancellation, giving equality on every displayed atom and hence
the usual almost-everywhere and L1 uniqueness consequences.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

/-- A retained cellwise observable integrates over a partition cell as its original cell probability times its retained
value. -/
theorem eventIntegral_cellwise {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (candidate : α → Fraction.Rational)
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
      · simp only [-eq_self, -iff_self, Distribution.indicator, selected, zero_mul]; try rfl
      · simp only [-eq_self, -iff_self, Distribution.indicator, selected, one_mul]; try rfl
        exact represented.agrees event eventMember atom atomMember selected
    _ = distribution.probability event * represented.cellValue event :=
      distribution.eventIntegral_constant event (represented.cellValue event)

/-- A retained cellwise observable has conditional mean equal to its retained value on every positive partition cell. -/
theorem conditionalMean_cellwise {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (candidate : α → Fraction.Rational)
    (represented : CellwiseObservable partition candidate)
    (event : α → Bool) (eventMember : event ∈ partition.events) :
    distribution.conditionalMean event candidate =
      represented.cellValue event := by
  let probability := distribution.probability event
  have positive : 0 < probability := partition.positive event eventMember
  apply Fraction.Field.mul_right_cancel_of_ne positive.ne'
  calc
    distribution.conditionalMean event candidate * probability =
        probability * distribution.conditionalMean event candidate := by
      ring1
    _ = distribution.eventIntegral event candidate :=
      distribution.probability_mul_conditionalMean event candidate positive
    _ = probability * represented.cellValue event :=
      partition.eventIntegral_cellwise candidate represented event eventMember
    _ = represented.cellValue event * probability := by ring1

/-- A cellwise candidate preserving all original cell integrals equals the partition conditional expectation on every
retained atom. -/
theorem candidate_eq_conditionalExpectation_on_atoms {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value candidate : α → Fraction.Rational)
    (represented : CellwiseObservable partition candidate)
    (preserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event candidate =
        distribution.eventIntegral event value) :
    ∀ atom, atom ∈ distribution.atoms →
      candidate atom.item = partition.conditionalExpectation value atom.item := by
  intro atom atomMember
  rcases partition.toEventPartition.exists_selected_event atom atomMember with
    ⟨event, eventMember, selected⟩
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

/-- A cellwise candidate preserving all original cell integrals agrees almost everywhere with the partition conditional
expectation. -/
theorem candidate_equalAlmostEverywhere_conditionalExpectation {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value candidate : α → Fraction.Rational)
    (represented : CellwiseObservable partition candidate)
    (preserves : ∀ event, event ∈ partition.events →
      distribution.eventIntegral event candidate =
        distribution.eventIntegral event value) :
    distribution.EqualAlmostEverywhere candidate
      (partition.conditionalExpectation value) := by
  intro atom atomMember
  exact Or.inr (partition.candidate_eq_conditionalExpectation_on_atoms
    value candidate represented preserves atom atomMember)

/-- A cellwise candidate preserving all original cell integrals has zero integrated distance from the partition
conditional expectation. -/
theorem l1Distance_candidate_conditionalExpectation_eq_zero {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value candidate : α → Fraction.Rational)
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

/-- Two cellwise candidates preserving the same original cell integrals agree on every retained distribution atom. -/
theorem characterized_candidates_eq_on_atoms {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value left right : α → Fraction.Rational)
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

end Purelib.Measure
