module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Weighted.Rat.Sort
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Constructive finite rational quantiles

A rational-valued finite distribution admits an executable lower quantile at
every displayed level in `(0, 1]`.  The implementation insertion-sorts the
displayed atom table and performs a terminating weighted crossing search.
The result is accompanied by the exact strict-lower and cumulative
inequalities; no infimum, completed real line, or choice principle occurs.
-/

namespace Purelib.Measure

open Purelib.Data.Rat in
/-- A strict lower cut has zero weight when every retained payload is at least its threshold. -/
theorem eventWeight_strictlyBelow_eq_zero
    (threshold : Fraction.Rational) :
    ∀ {atoms : List (Weighted Fraction.Rational)},
      (∀ atom, atom ∈ atoms → threshold ≤ atom.item) →
      eventWeight atoms (strictlyBelowEvent threshold) = 0
  | [], bounded => rfl
  | atom :: remaining, bounded => by
      have headOrder := bounded atom List.mem_cons_self
      have headNotBelow : ¬atom.item < threshold :=
        fun below => below.2 headOrder
      have tailBounded : ∀ candidate, candidate ∈ remaining →
          threshold ≤ candidate.item :=
        fun candidate member =>
          bounded candidate (List.mem_cons_of_mem atom member)
      have selected : strictlyBelowEvent threshold atom.item = false :=
        decide_eq_false headNotBelow
      rw [eventWeight, selected, zero_add,
        eventWeight_strictlyBelow_eq_zero threshold tailBounded]

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a positive-weight original occurrence whose value crosses the supplied cumulative mass level.

The exact selected occurrence belongs to the same weighted list. Strictly lower payloads have mass below the level,
while the weak cut through its threshold has mass at least that level. -/
structure SortedQuantileCertificate
    (atoms : List (Weighted Fraction.Rational)) (level : Fraction.Rational) where
  /-- The exact rational payload value selected as the quantile threshold. -/ threshold : Fraction.Rational
  /-- The original weighted occurrence selected at the crossing. -/ selectedAtom : Weighted Fraction.Rational
  /-- The selected occurrence belongs to the same retained input list. -/ selectedMember : selectedAtom ∈ atoms
  /-- The selected occurrence's payload equals the retained threshold. -/ selectedValue : selectedAtom.item = threshold
  /-- The selected original occurrence has strictly positive weight. -/ selectedPositive : 0 < selectedAtom.weight
  /-- The retained list's weight strictly below the threshold is less than the level. -/ below : eventWeight atoms
    (strictlyBelowEvent threshold) < level
  /-- The retained list's weight at most the threshold is at least the level. -/ cumulative : level ≤ eventWeight atoms
    (atMostEvent threshold)

constructive_injectivity SortedQuantileCertificate

open Purelib.Data.Rat
/-- Scan retained weights until the level is at most the next weight, subtracting earlier weights recursively.

Return that exact payload; the empty-list fallback is zero. This numerical readback uses the original occurrence order
and does not require the certified sortedness or level bounds. -/
@[expose] def sortedQuantileThreshold :
    List (Weighted Fraction.Rational) → Fraction.Rational → Fraction.Rational
  | [], _ => 0
  | atom :: remaining, level =>
      if level ≤ atom.weight then atom.item
      else sortedQuantileThreshold remaining (level - atom.weight)

/-- Construct a quantile certificate from the exact sorted weighted list and a positive level at most its total.

The first crossing retains its original positive-weight occurrence. Otherwise recurse on the same tail with the head
weight subtracted, transporting its membership and strict/weak cut bounds back to the original list. -/
@[expose] def sortedQuantile :
    (atoms : List (Weighted Fraction.Rational)) →
    ValueSorted atoms →
    (level : Fraction.Rational) → 0 < level → level ≤ totalWeight atoms →
    SortedQuantileCertificate atoms level
  | [], sorted, level, positive, bounded => by
      exact (positive.2 bounded).elim
  | atom :: remaining, sorted, level, positive, bounded => by
      rcases sorted with ⟨headLower, tailSorted⟩
      by_cases crosses : level ≤ atom.weight
      · refine
          { threshold := atom.item
            selectedAtom := atom
            selectedMember := List.mem_cons_self
            selectedValue := rfl
            selectedPositive := positive.trans_le crosses
            below := ?_
            cumulative := ?_ }
        · have allLower : ∀ candidate,
              candidate ∈ atom :: remaining → atom.item ≤ candidate.item := by
            intro candidate member
            cases member with
            | head => exact le_rfl
            | tail _ tail => exact headLower candidate tail
          rw [eventWeight_strictlyBelow_eq_zero atom.item allLower]
          exact positive
        · have selected : atMostEvent atom.item atom.item = true :=
            decide_eq_true (le_rfl : atom.item ≤ atom.item)
          rw [eventWeight, selected]
          exact crosses.trans
            (le_add_of_nonneg_right
              (eventWeight_nonneg remaining (atMostEvent atom.item)))
      · let adjusted := level - atom.weight
        have atomLessLevel : atom.weight < level :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct crosses
        have adjustedPositive : 0 < adjusted :=
          Fraction.Order.Arithmetic.sub_pos_direct atomLessLevel
        have adjustedBounded : adjusted ≤ totalWeight remaining := by
          have shifted :=
            Fraction.Order.Arithmetic.add_le_add_right_direct bounded
              (-atom.weight)
          calc
            adjusted = level + -atom.weight := by
              dsimp only [adjusted]
              ring1
            _ ≤ (atom.weight + totalWeight remaining) + -atom.weight :=
              shifted
            _ = totalWeight remaining := by ring1
        let tailResult := sortedQuantile remaining tailSorted adjusted
          adjustedPositive adjustedBounded
        have headLeThreshold : atom.item ≤ tailResult.threshold := by
          rw [← tailResult.selectedValue]
          exact headLower tailResult.selectedAtom tailResult.selectedMember
        let headContribution : Fraction.Rational :=
          match strictlyBelowEvent tailResult.threshold atom.item with
          | true => atom.weight
          | false => 0
        have headContributionLe : headContribution ≤ atom.weight := by
          dsimp only [headContribution]
          cases strictlyBelowEvent tailResult.threshold atom.item
          · exact atom.nonnegative
          · exact le_rfl
        refine
          { threshold := tailResult.threshold
            selectedAtom := tailResult.selectedAtom
            selectedMember :=
              List.mem_cons_of_mem atom tailResult.selectedMember
            selectedValue := tailResult.selectedValue
            selectedPositive := tailResult.selectedPositive
            below := ?_
            cumulative := ?_ }
        · change headContribution +
              eventWeight remaining
                (strictlyBelowEvent tailResult.threshold) < level
          calc
            headContribution +
                  eventWeight remaining
                    (strictlyBelowEvent tailResult.threshold) ≤
                atom.weight +
                  eventWeight remaining
                    (strictlyBelowEvent tailResult.threshold) :=
              Fraction.Order.Arithmetic.add_le_add_direct
                headContributionLe le_rfl
            _ < atom.weight + adjusted :=
              Fraction.Order.Arithmetic.add_lt_add_left_direct
                tailResult.below atom.weight
            _ = level := by
              dsimp only [adjusted]
              ring1
        · have headSelected :
              atMostEvent tailResult.threshold atom.item = true :=
            decide_eq_true headLeThreshold
          simp only [-eq_self, -iff_self, eventWeight, headSelected]
          calc
            level = atom.weight + adjusted := by
              dsimp only [adjusted]
              ring1
            _ ≤ atom.weight +
                  eventWeight remaining
                    (atMostEvent tailResult.threshold) :=
              Fraction.Order.Arithmetic.add_le_add_direct le_rfl
                tailResult.cumulative

/-- The certified sorted quantile returns exactly the threshold computed by the retained numerical scan.

Both procedures follow the same first cumulative crossing and subtract the
same original weights. The sortedness and positive level bounds justify the
certificate while its threshold retains that numerical selection. -/
theorem sortedQuantile_threshold_eq :
    ∀ (atoms : List (Weighted Fraction.Rational))
      (sorted : ValueSorted atoms)
      (level : Fraction.Rational) (positive : 0 < level)
      (bounded : level ≤ totalWeight atoms),
      (sortedQuantile atoms sorted level positive bounded).threshold =
        sortedQuantileThreshold atoms level
  | [], sorted, level, positive, bounded => by
      exact (positive.2 bounded).elim
  | atom :: remaining, sorted, level, positive, bounded => by
      rcases sorted with ⟨headLower, tailSorted⟩
      by_cases crosses : level ≤ atom.weight
      · dsimp only [sortedQuantile, sortedQuantileThreshold]
        rw [dif_pos crosses, if_pos crosses]
      · let adjusted := level - atom.weight
        have atomLessLevel : atom.weight < level :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct crosses
        have adjustedPositive : 0 < adjusted :=
          Fraction.Order.Arithmetic.sub_pos_direct atomLessLevel
        have adjustedBounded : adjusted ≤ totalWeight remaining := by
          have shifted :=
            Fraction.Order.Arithmetic.add_le_add_right_direct bounded
              (-atom.weight)
          calc
            adjusted = level + -atom.weight := by
              dsimp only [adjusted]
              ring1
            _ ≤ (atom.weight + totalWeight remaining) + -atom.weight :=
              shifted
            _ = totalWeight remaining := by ring1
        dsimp only [sortedQuantile, sortedQuantileThreshold]
        rw [dif_neg crosses, if_neg crosses]
        exact sortedQuantile_threshold_eq remaining tailSorted adjusted
          adjustedPositive adjustedBounded
end Purelib.Measure

end
