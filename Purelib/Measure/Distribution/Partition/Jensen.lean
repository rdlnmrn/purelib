module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Lp.L1
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Expectation
import Purelib.Measure.Distribution.Partition.Moments
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Weighted.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Conditioning.Jensen
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Finite conditional Jensen inequalities

Conditioning and conditional expectation are finite rational averages.
Jensen's supporting-line proof therefore applies cellwise without any
measurable-function space or limiting argument.  Squaring gives fully
explicit cellwise and partition-level second-moment contraction.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace Distribution
end Distribution

namespace PositiveEventPartition

/-- Cell-specific supporting lines give Jensen's inequality for partition conditional expectation at every retained
atom. -/
theorem conditionalJensen_on_atoms_of_supportingLines {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (transform : Fraction.Rational → Fraction.Rational)
    (slope : (α → Bool) → Fraction.Rational)
    (supports : ∀ event, event ∈ partition.events →
      ∀ atom, atom ∈ distribution.atoms → event atom.item = true →
        transform (distribution.conditionalMean event value) +
            slope event * (value atom.item -
              distribution.conditionalMean event value) ≤
          transform (value atom.item))
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    transform (partition.conditionalExpectation value atom.item) ≤
      partition.conditionalExpectation
        (fun item => transform (value item)) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => transform (value item)) event eventMember atom member
      selected]
  exact distribution.conditionalJensen_of_supportingLine_on_event event
    (partition.positive event eventMember) value transform (slope event)
    (supports event eventMember)

/-- The magnitude of partition conditional expectation is bounded atomwise by the conditional expectation of original
magnitude. -/
theorem rationalSeparation_conditionalExpectation_zero_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    Distance.rationalSeparation
        (partition.conditionalExpectation value atom.item) 0 ≤
      partition.conditionalExpectation
        (fun item => Distance.rationalSeparation (value item) 0) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => Distance.rationalSeparation (value item) 0) event eventMember atom
      member selected]
  exact distribution.conditionalMean_rationalSeparation_zero_le event
    (partition.positive event eventMember) value

/-- Squared partition conditional expectation is bounded atomwise by the conditional expectation of the square. -/
theorem conditionalExpectation_sq_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation value atom.item ^ 2 ≤
      partition.conditionalExpectation
        (fun item => value item ^ 2) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => value item ^ 2) event eventMember atom member selected]
  exact distribution.conditionalMean_sq_le event
    (partition.positive event eventMember) value

/-- Partition conditional expectation cannot increase magnitude expectation. -/
theorem poweredL1_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    distribution.poweredL1 (partition.conditionalExpectation value) ≤
      distribution.poweredL1 value := by
  change distribution.expectation (fun item => Distance.rationalSeparation
      (partition.conditionalExpectation value item) 0) ≤
    distribution.expectation (fun item => Distance.rationalSeparation (value item) 0)
  calc
    distribution.expectation (fun item => Distance.rationalSeparation
          (partition.conditionalExpectation value item) 0) ≤
        distribution.expectation
          (partition.conditionalExpectation (fun item =>
            Distance.rationalSeparation (value item) 0)) := by
      apply distribution.expectation_mono
      intro atom member
      exact partition.rationalSeparation_conditionalExpectation_zero_le
        value atom member
    _ = distribution.expectation (fun item =>
          Distance.rationalSeparation (value item) 0) :=
      partition.expectation_conditionalExpectation _

/-- Partition conditional expectation cannot increase integrated distance between two observables. -/
theorem l1Distance_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    distribution.l1Distance
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) ≤
      distribution.l1Distance left right := by
  have contraction := partition.poweredL1_conditionalExpectation_le
    (fun item => left item - right item)
  have conditionalDifference :=
    distribution.toContent.poweredL1_congr
      (partition.conditionalExpectation (fun item => left item - right item))
      (fun item => partition.conditionalExpectation left item -
        partition.conditionalExpectation right item)
      (partition.conditionalExpectation_sub left right)
  change distribution.poweredL1
      (partition.conditionalExpectation (fun item => left item - right item)) =
    distribution.poweredL1 (fun item =>
      partition.conditionalExpectation left item -
        partition.conditionalExpectation right item) at conditionalDifference
  rw [conditionalDifference,
    distribution.poweredL1_sub_eq_l1Distance,
    distribution.poweredL1_sub_eq_l1Distance] at contraction
  exact contraction

/-- Partition conditional expectation cannot increase the squared-observable expectation. -/
theorem expectation_sq_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    distribution.expectation (fun item =>
        partition.conditionalExpectation value item ^ 2) ≤
      distribution.expectation (fun item => value item ^ 2) := by
  have varianceBound := partition.variance_conditionalExpectation_le value
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    partition.expectation_conditionalExpectation value] at varianceBound
  calc
    distribution.expectation (fun item =>
          partition.conditionalExpectation value item ^ 2) =
        (distribution.expectation (fun item =>
            partition.conditionalExpectation value item ^ 2) -
          distribution.expectation value ^ 2) +
            distribution.expectation value ^ 2 := by ring1
    _ ≤ (distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2) +
            distribution.expectation value ^ 2 :=
      add_le_add varianceBound le_rfl
    _ = distribution.expectation (fun item => value item ^ 2) := by ring1

end PositiveEventPartition

end Purelib.Measure

end
