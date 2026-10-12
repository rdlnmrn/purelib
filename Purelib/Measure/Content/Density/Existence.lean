module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Content.Equivalence
public import Purelib.Measure.Content.Histogram
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
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

@[expose] public section

namespace Purelib.Measure

/-- A payload absent from the exact key list remains absent after attaching source and target singleton masses. -/
private theorem atomicRowPayloadAbsent_map_atomMass {α : Type}
    [DecidableEq α] (source target : Content α)
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

/-- Distinct exact keys remain distinct aligned rows after attaching their two original singleton masses. -/
private theorem noRepeatedAtomicRows_map_atomMass {α : Type}
    [DecidableEq α] (source target : Content α)
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

section
open Purelib.Data.Rat
/-- Source readback from singleton-mass rows integrates as the original source's exact key-indexed mass sum. -/
private theorem expectationWeight_sourceAtoms_map_atomMass {α : Type}
    [DecidableEq α] (source target : Content α)
    (continuous : target.AbsolutelyContinuous source)
    (value : α → Fraction.Rational) :
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
      simp only [-eq_self, -iff_self, List.map_cons, AtomicChange.sourceAtoms,
        Distribution.expectationWeight, Content.atomMassSum,
        expectationWeight_sourceAtoms_map_atomMass source target continuous
          value remaining]
      rfl

/-- Target readback from singleton-mass rows integrates as the original target's exact key-indexed mass sum. -/
private theorem expectationWeight_targetAtoms_map_atomMass {α : Type}
    [DecidableEq α] (source target : Content α)
    (continuous : target.AbsolutelyContinuous source)
    (value : α → Fraction.Rational) :
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
      simp only [-eq_self, -iff_self, List.map_cons, AtomicChange.targetAtoms,
        Distribution.expectationWeight, Content.atomMassSum,
        expectationWeight_targetAtoms_map_atomMass source target continuous
          value remaining]
      rfl

end

namespace AtomicChange

/-- Construct aligned rows from the shared consolidated keys and original source-target singleton masses.

Absolute continuity supplies zero transfer at each key. The same finite key list supplies distinctness and both exact
mass readbacks. -/
def ofAbsolutelyContinuous {α : Type} [DecidableEq α]
    (source target : Content α)
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

/-- The aligned singleton-mass source is evaluation equivalent to the original source content. -/
theorem ofAbsolutelyContinuous_source_evaluationEquivalent {α : Type}
    [DecidableEq α] (source target : Content α)
    (continuous : target.AbsolutelyContinuous source) :
    Content.EvaluationEquivalent
      (ofAbsolutelyContinuous source target continuous).source source := by
  apply Content.EvaluationEquivalent.of_integral_eq
  intro value
  unfold AtomicChange.source ofAbsolutelyContinuous Content.integral
  rw [expectationWeight_sourceAtoms_map_atomMass source target continuous
    value]
  exact source.atomMassSum_eq_integral value
    (source.radonNikodymKeys target)
    (source.radonNikodymKeys_noRepeated target)
    (source.payloadsCovered_radonNikodymKeys_left target)

/-- The aligned singleton-mass target is evaluation equivalent to the original target content. -/
theorem ofAbsolutelyContinuous_target_evaluationEquivalent {α : Type}
    [DecidableEq α] (source target : Content α)
    (continuous : target.AbsolutelyContinuous source) :
    Content.EvaluationEquivalent
      (ofAbsolutelyContinuous source target continuous).target target := by
  apply Content.EvaluationEquivalent.of_integral_eq
  intro value
  unfold AtomicChange.target ofAbsolutelyContinuous Content.integral
  rw [expectationWeight_targetAtoms_map_atomMass source target continuous
    value]
  exact target.atomMassSum_eq_integral value
    (source.radonNikodymKeys target)
    (source.radonNikodymKeys_noRepeated target)
    (source.payloadsCovered_radonNikodymKeys_right target)

end AtomicChange

end Purelib.Measure

end
