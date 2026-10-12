module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.List.Event
import Purelib.Data.List.Multiplicity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.Event.Singleton
import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Operations
public import Purelib.Measure.Weighted.Unit
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Measure

open Purelib in
open Purelib.Data.Rat in
/-- Assign equal weight to every occurrence in the exact nonempty sample list.

The original order and repeated payloads remain unchanged, and the retained positive-length certificate justifies
normalization by that same length. -/
def empiricalDistribution {α : Type} (samples : List α)
    (positiveLength : 0 < samples.length) : Measure.Distribution α where
  atoms := scaleAtoms
    (1 / (samples.length : Fraction.Rational))
    (Fraction.Order.Field.div_nonneg_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct positiveLength).le)
    (unitAtoms samples)
  total_one := by
    rw [totalWeight_scaleAtoms, totalWeight_unitAtoms]
    exact Fraction.Field.div_mul_cancel_of_ne 1
      (samples.length : Fraction.Rational)
      (Fraction.Cast.Order.natCast_pos_direct positiveLength).ne'

open Purelib in
/-- Every retained empirical atom payload occurs in the original sample list. -/
theorem empiricalDistribution_atom_sampleContains {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (candidate : Weighted α)
    (member : candidate ∈
      (empiricalDistribution samples positiveLength).atoms) :
    Data.List.SampleContains candidate.item samples := by
  unfold empiricalDistribution at member
  rcases mem_scaleAtoms_source _ _ candidate member with
      ⟨source, sourceMember, itemEqual⟩
  simpa only [itemEqual] using
    unitAtoms_member_sampleContains source sourceMember

/-- The exact empirical law has one atom occurrence per original sample occurrence. -/
theorem empiricalDistribution_atoms_length {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length) :
    (empiricalDistribution samples positiveLength).atoms.length =
      samples.length := by
  simp only [-eq_self, -iff_self, empiricalDistribution, scaleAtoms_length, unitAtoms_length]
  rfl

section
open Purelib
open Purelib.Data.Rat
/-- Empirical event probability equals the original selected sample count divided by original sample length. -/
theorem empiricalDistribution_probability {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (event : α → Bool) :
    (empiricalDistribution samples positiveLength).probability event =
      (Data.List.countEvent samples event : Fraction.Rational) /
        (samples.length : Fraction.Rational) := by
  unfold Distribution.probability empiricalDistribution
  rw [eventWeight_scaleAtoms, eventWeight_unitAtoms]
  change (1 * (samples.length : Fraction.Rational)⁻¹) *
      (Data.List.countEvent samples event : Fraction.Rational) =
    (Data.List.countEvent samples event : Fraction.Rational) *
      (samples.length : Fraction.Rational)⁻¹
  rw [Fraction.Field.one_mul]
  exact Fraction.Field.mul_comm _ _

/-- Empirical mass at an item equals its singleton-event sample count divided by original sample length. -/
theorem empiricalDistribution_atomMass {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalDistribution samples positiveLength).atomMass item =
      (Data.List.countEvent samples (atomEvent item) : Fraction.Rational) /
        (samples.length : Fraction.Rational) :=
  empiricalDistribution_probability samples positiveLength (atomEvent item)

/-- Empirical mass at an item equals its original multiplicity divided by original sample length. -/
theorem empiricalDistribution_atomMass_eq_countItem
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalDistribution samples positiveLength).atomMass item =
      (Data.List.countItem samples item : Fraction.Rational) /
        (samples.length : Fraction.Rational) := by
  rw [empiricalDistribution_atomMass, countEvent_atomEvent]

/-- An item absent from the original sample list has zero empirical mass. -/
theorem empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α)
    (absent : Data.List.SampleAbsent item samples) :
    (empiricalDistribution samples positiveLength).atomMass item = 0 := by
  rw [empiricalDistribution_atomMass_eq_countItem,
    Data.List.countItem_eq_zero_of_sampleAbsent item samples absent, Nat.cast_zero]
  exact Fraction.Field.zero_div_direct _

/-- An item occurring in the original sample list has strictly positive empirical mass. -/
theorem empiricalDistribution_atomMass_pos_of_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α)
    (contains : Data.List.SampleContains item samples) :
    0 < (empiricalDistribution samples positiveLength).atomMass item := by
  rw [empiricalDistribution_atomMass_eq_countItem]
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct
      (Data.List.countItem_pos_of_sampleContains item samples contains))
    (Fraction.Cast.Order.natCast_pos_direct positiveLength)

end

section
open Purelib
/-- Empirical mass is zero exactly for items absent from the original sample list. -/
theorem empiricalDistribution_atomMass_eq_zero_iff_sampleAbsent
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalDistribution samples positiveLength).atomMass item = 0 ↔
      Data.List.SampleAbsent item samples := by
  constructor
  · intro massZero
    rcases Data.List.sampleContains_or_sampleAbsent item samples with
        contains | absent
    · have positive :=
        empiricalDistribution_atomMass_pos_of_sampleContains
          samples positiveLength item contains
      rw [massZero] at positive
      exact (positive.2 le_rfl).elim
    · exact absent
  · exact empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
      samples positiveLength item

/-- Empirical mass is positive exactly for items occurring in the original sample list. -/
theorem empiricalDistribution_atomMass_pos_iff_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    0 < (empiricalDistribution samples positiveLength).atomMass item ↔
      Data.List.SampleContains item samples := by
  constructor
  · intro positive
    rcases Data.List.sampleContains_or_sampleAbsent item samples with
        contains | absent
    · exact contains
    · have massZero :=
        empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
          samples positiveLength item absent
      rw [massZero] at positive
      exact (positive.2 le_rfl).elim
  · exact empiricalDistribution_atomMass_pos_of_sampleContains
      samples positiveLength item

end

section
open Purelib.Data.Rat
/-- Empirical expectation equals the exact original value sum divided by original sample length. -/
theorem empiricalDistribution_expectation {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).expectation value =
      sumValues samples value / (samples.length : Fraction.Rational) := by
  unfold Distribution.expectation empiricalDistribution
  rw [expectationWeight_scaleAtoms, expectationWeight_unitAtoms]
  change (1 * (samples.length : Fraction.Rational)⁻¹) * sumValues samples value =
    sumValues samples value * (samples.length : Fraction.Rational)⁻¹
  rw [Fraction.Field.one_mul]
  exact Fraction.Field.mul_comm _ _

/-- Empirical expectation equals the sample mean computed on the same exact sample list and length. -/
theorem empiricalDistribution_expectation_eq_sampleMean {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Fraction.Rational) :
    (empiricalDistribution samples positiveLength).expectation value =
      Distribution.sampleMean samples.length value samples := by
  rw [empiricalDistribution_expectation,
    sumValues_eq_sampleSum]
  unfold Distribution.sampleMean
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.mul_comm]

end

/-- Empirical event probability equals the event frequency computed on the same exact sample list and length. -/
theorem empiricalDistribution_probability_eq_eventFrequency {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (event : α → Bool) :
    (empiricalDistribution samples positiveLength).probability event =
      Distribution.eventFrequency samples.length event samples := by
  rw [← (empiricalDistribution samples positiveLength).expectation_indicator]
  unfold Distribution.eventFrequency
  exact empiricalDistribution_expectation_eq_sampleMean samples
    positiveLength (Distribution.indicator event)
end Purelib.Measure

end
