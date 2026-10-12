module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.List.Multiplicity
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Consolidation
public import Purelib.Measure.Distribution.Empirical.Basic
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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
/-- Consolidate the exact nonempty sample's empirical law into one atom per distinct payload.

The construction uses the original empirical weights and the retained decidable equality to merge repeated payloads
while preserving evaluations. -/
def empiricalHistogram {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    Measure.Distribution α :=
  (empiricalDistribution samples positiveLength).consolidate

/-- The exact consolidated histogram is evaluation-equivalent to the original occurrence-preserving empirical law. -/
theorem empiricalHistogram_evaluationEquivalent
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    Distribution.EvaluationEquivalent
      (empiricalHistogram samples positiveLength)
      (empiricalDistribution samples positiveLength) :=
  (empiricalDistribution samples positiveLength).consolidate_evaluationEquivalent

/-- The exact consolidated histogram has at most the original number of sample occurrences. -/
theorem empiricalHistogram_atoms_length_le
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    (empiricalHistogram samples positiveLength).atoms.length ≤
      samples.length := by
  calc
    (empiricalHistogram samples positiveLength).atoms.length ≤
        (empiricalDistribution samples positiveLength).atoms.length :=
      (empiricalDistribution samples positiveLength).consolidate_atoms_length_le
    _ = samples.length :=
      empiricalDistribution_atoms_length samples positiveLength

/-- The exact empirical histogram has no repeated atom payloads. -/
theorem empiricalHistogram_noRepeatedPayloads
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    NoRepeatedPayloads (empiricalHistogram samples positiveLength).atoms :=
  (empiricalDistribution samples positiveLength).consolidate_noRepeatedPayloads

section
open Purelib
open Purelib.Data.Rat
/-- Histogram mass at an item is its original sample multiplicity divided by original sample length. -/
theorem empiricalHistogram_atomMass_eq_countItem
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalHistogram samples positiveLength).atomMass item =
      (Data.List.countItem samples item : Fraction.Rational) /
        (samples.length : Fraction.Rational) := by
  rw [empiricalHistogram,
    Distribution.consolidate_atomMass,
    empiricalDistribution_atomMass_eq_countItem]

/-- An item occurring in the original sample list has positive mass in its exact histogram. -/
theorem empiricalHistogram_atomMass_pos_of_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α)
    (contains : Data.List.SampleContains item samples) :
    0 < (empiricalHistogram samples positiveLength).atomMass item := by
  rw [empiricalHistogram_atomMass_eq_countItem]
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct
      (Data.List.countItem_pos_of_sampleContains item samples contains))
    (Fraction.Cast.Order.natCast_pos_direct positiveLength)

end

open Purelib in
/-- Positive histogram mass is equivalent to occurrence in the exact original sample list. -/
theorem empiricalHistogram_atomMass_pos_iff_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    0 < (empiricalHistogram samples positiveLength).atomMass item ↔
      Data.List.SampleContains item samples := by
  unfold empiricalHistogram
  rw [Distribution.consolidate_atomMass]
  exact empiricalDistribution_atomMass_pos_iff_sampleContains
    samples positiveLength item
end Purelib.Measure

end
