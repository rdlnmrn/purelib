module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Weighted.Rat.Quantile
import Purelib.Measure.Weighted.Rat.Sort
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Equivalence
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

open Purelib.Data

open Purelib in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a positive-weight original atom whose value crosses the exact distribution's supplied quantile level.

Probability strictly below the retained threshold is less than the level, while cumulative probability at that threshold
is at least the level. -/
structure QuantileCertificate (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) where
  /-- The exact retained rational quantile threshold. -/ threshold : Fraction.Rational
  /-- The original positive-weight atom selected at the threshold crossing. -/ selectedAtom : Measure.Weighted
    Fraction.Rational
  /-- The selected occurrence belongs to the exact original distribution atom list. -/ selectedMember : selectedAtom ∈
    distribution.atoms
  /-- The selected atom's payload is the exact retained threshold. -/ selectedValue : selectedAtom.item = threshold
  /-- The retained selected atom has strictly positive original weight. -/ selectedPositive : 0 < selectedAtom.weight
  /-- Original probability strictly below the retained threshold is less than the supplied level. -/
    probability_strictlyBelow_lt :
    distribution.probability (strictlyBelowEvent threshold) < level
  /-- Original cumulative probability at the retained threshold reaches the supplied level. -/ level_le_cumulative :
    level ≤ distribution.cumulative threshold

constructive_injectivity QuantileCertificate

section
open Purelib
open Purelib.Data.Rat
/-- Compute a quantile crossing certificate by sorting the exact original atom list and retaining the selected original
occurrence.

The supplied level is positive and at most one; the certificate preserves its threshold, original membership and
positive-weight witness. -/
@[expose] def Distribution.quantileCertificate
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    QuantileCertificate distribution level := by
  let sortedAtoms := sortByValue distribution.atoms
  have sortFacts := sortByValue_certificates distribution.atoms
  have sorted : ValueSorted sortedAtoms := sortFacts.1
  have bounded : level ≤ totalWeight sortedAtoms := by
    rw [sortFacts.2.1, distribution.total_one]
    exact atMostOne
  let result := sortedQuantile sortedAtoms sorted level positive bounded
  have resultThreshold : result.threshold =
      sortedQuantileThreshold sortedAtoms level :=
    sortedQuantile_threshold_eq sortedAtoms sorted level positive bounded
  exact
    { threshold := sortedQuantileThreshold sortedAtoms level
      selectedAtom := result.selectedAtom
      selectedMember :=
        sortFacts.2.2.1 result.selectedAtom result.selectedMember
      selectedValue := result.selectedValue.trans resultThreshold
      selectedPositive := result.selectedPositive
      probability_strictlyBelow_lt := by
        unfold Distribution.probability
        rw [← sortFacts.2.2.2 (strictlyBelowEvent
          (sortedQuantileThreshold sortedAtoms level))]
        rw [← resultThreshold]
        exact result.below
      level_le_cumulative := by
        unfold Distribution.cumulative Distribution.probability
        rw [← sortFacts.2.2.2 (atMostEvent
          (sortedQuantileThreshold sortedAtoms level))]
        rw [← resultThreshold]
        exact result.cumulative }

/-- Compute the first sorted-atom threshold whose accumulated weight reaches the supplied level.

The original level is certified positive and at most one, and sorting uses the exact retained distribution atom list. -/
@[expose] def Distribution.lowerQuantile
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (_positive : 0 < level) (_atMostOne : level ≤ 1) :
    Fraction.Rational :=
  sortedQuantileThreshold (sortByValue distribution.atoms) level

/-- The exact lower quantile equals the payload of an original retained atom. -/
theorem Distribution.lowerQuantile_eq_atom_of_mem
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    ∃ atom, atom ∈ distribution.atoms ∧
      atom.item = distribution.lowerQuantile level positive atMostOne := by
  let certificate := distribution.quantileCertificate level positive atMostOne
  exact ⟨certificate.selectedAtom, certificate.selectedMember,
    certificate.selectedValue⟩

/-- The exact lower quantile equals the payload of an original retained positive-weight atom. -/
theorem Distribution.lowerQuantile_eq_positiveAtom_of_mem
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    ∃ atom, atom ∈ distribution.atoms ∧ 0 < atom.weight ∧
      atom.item = distribution.lowerQuantile level positive atMostOne := by
  let certificate := distribution.quantileCertificate level positive atMostOne
  exact ⟨certificate.selectedAtom, certificate.selectedMember,
    certificate.selectedPositive, certificate.selectedValue⟩

/-- Probability strictly below the computed lower quantile is strictly less than its original level. -/
theorem Distribution.probability_strictlyBelow_lowerQuantile_lt
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    distribution.probability
        (strictlyBelowEvent
          (distribution.lowerQuantile level positive atMostOne)) < level :=
  (distribution.quantileCertificate level positive atMostOne)
    |>.probability_strictlyBelow_lt

/-- Cumulative probability at the computed lower quantile is at least its original level. -/
theorem Distribution.level_le_cumulative_lowerQuantile
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    level ≤ distribution.cumulative
      (distribution.lowerQuantile level positive atMostOne) :=
  (distribution.quantileCertificate level positive atMostOne)
    |>.level_le_cumulative

/-- Cumulative probability at the exact level-one lower quantile is one. -/
theorem Distribution.cumulative_lowerQuantile_one_eq_one
    (distribution : Measure.Distribution Fraction.Rational) :
    distribution.cumulative
      (distribution.lowerQuantile 1 (by decide) le_rfl) = 1 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact distribution.cumulative_le_one _
  · exact distribution.level_le_cumulative_lowerQuantile
      1 (by decide) le_rfl

/-- Every retained positive-weight atom lies at or below the exact level-one lower quantile. -/
theorem Distribution.positiveAtom_le_lowerQuantile_one
    (distribution : Measure.Distribution Fraction.Rational)
    (atom : Measure.Weighted Fraction.Rational) (member : atom ∈ distribution.atoms)
    (weightPositive : 0 < atom.weight) :
    atom.item ≤ distribution.lowerQuantile 1 (by decide) le_rfl := by
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro quantileLtAtom
  let maximum := distribution.lowerQuantile 1 (by decide) le_rfl
  have notAtMost : atMostEvent maximum atom.item = false := by
    exact decide_eq_false quantileLtAtom.2
  have complementSelected : complementEvent (atMostEvent maximum)
      atom.item = true := by
    change Bool.not (atMostEvent maximum atom.item) = true
    rw [notAtMost]
    rfl
  have sum := distribution.probability_add_complement (atMostEvent maximum)
  have cumulativeOne : distribution.probability (atMostEvent maximum) = 1 :=
    distribution.cumulative_lowerQuantile_one_eq_one
  rw [cumulativeOne] at sum
  have complementZero :
      distribution.probability (complementEvent (atMostEvent maximum)) = 0 := by
    calc
      distribution.probability (complementEvent (atMostEvent maximum)) =
          (1 + distribution.probability
            (complementEvent (atMostEvent maximum))) - 1 := by ring1
      _ = 1 - 1 := congrArg (fun value => value - 1) sum
      _ = 0 := by ring1
  have weightLe := atom_weight_le_eventWeight_of_mem member complementSelected
  change atom.weight ≤
    distribution.probability (complementEvent (atMostEvent maximum))
    at weightLe
  rw [complementZero] at weightLe
  exact (weightPositive.2 weightLe).elim

/-- Every cut at or above the exact level-one lower quantile has cumulative probability one. -/
theorem Distribution.cumulative_eq_one_of_lowerQuantile_one_le
    (distribution : Measure.Distribution Fraction.Rational) (cut : Fraction.Rational)
    (upper : distribution.lowerQuantile 1 (by decide) le_rfl ≤ cut) :
    distribution.cumulative cut = 1 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact distribution.cumulative_le_one cut
  · rw [← distribution.cumulative_lowerQuantile_one_eq_one]
    exact distribution.cumulative_mono upper

/-- A certified quantile threshold lies at or below a cut exactly when cumulative probability there reaches its level.
-/
theorem QuantileCertificate.threshold_le_iff_level_le_cumulative
    {distribution : Measure.Distribution Fraction.Rational} {level : Fraction.Rational}
    (certificate : QuantileCertificate distribution level)
    (cut : Fraction.Rational) :
    certificate.threshold ≤ cut ↔ level ≤ distribution.cumulative cut := by
  constructor
  · intro thresholdLe
    exact certificate.level_le_cumulative.trans
      (distribution.cumulative_mono thresholdLe)
  · intro levelLe
    apply Fraction.Order.Arithmetic.le_of_not_gt_direct
    intro cutLtThreshold
    have cumulativeLeBelow : distribution.cumulative cut ≤
        distribution.probability
          (strictlyBelowEvent certificate.threshold) := by
      apply eventWeight_mono
      intro atom member selected
      have atomLeCut : atom.item ≤ cut := of_decide_eq_true selected
      exact decide_eq_true (atomLeCut.trans_lt cutLtThreshold)
    exact certificate.probability_strictlyBelow_lt.2
      (levelLe.trans cumulativeLeBelow)

/-- Quantile certificates for the same exact law have monotone thresholds as their levels increase. -/
theorem QuantileCertificate.threshold_mono
    {distribution : Measure.Distribution Fraction.Rational}
    {lowerLevel upperLevel : Fraction.Rational}
    (lower : QuantileCertificate distribution lowerLevel)
    (upper : QuantileCertificate distribution upperLevel)
    (levels : lowerLevel ≤ upperLevel) :
    lower.threshold ≤ upper.threshold := by
  apply (lower.threshold_le_iff_level_le_cumulative upper.threshold).2
  exact levels.trans upper.level_le_cumulative
end

end Purelib.Measure

end
section
section
public section

/-!
# Uniform stability of constructive finite quantiles

Finite lower quantiles are stable under a displayed uniform rational
perturbation of the source observable.  The proof compares the two executable
cumulative events atom by atom and applies the exact finite generalized-inverse
law.  No infimum, limiting distribution, or completed metric space occurs.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- The computed lower quantile lies at or below a cut exactly when original cumulative probability there reaches its
level. -/
theorem lowerQuantile_le_iff_level_le_cumulative
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut : Fraction.Rational) :
    distribution.lowerQuantile level positive atMostOne ≤ cut ↔
      level ≤ distribution.cumulative cut :=
  (distribution.quantileCertificate level positive atMostOne)
    |>.threshold_le_iff_level_le_cumulative cut

/-- A support gap and cumulative level crossing force the exact computed lower quantile to equal the supplied upper gap
value. -/
theorem lowerQuantile_eq_of_atom_gap_crossing
    (distribution : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower value : Fraction.Rational)
    (gap : ∀ atom, atom ∈ distribution.atoms →
      atom.item ≤ lower ∨ value ≤ atom.item)
    (belowLevel : distribution.cumulative lower < level)
    (levelAtValue : level ≤ distribution.cumulative value) :
    distribution.lowerQuantile level positive atMostOne = value := by
  have quantileLeValue :
      distribution.lowerQuantile level positive atMostOne ≤ value :=
    (distribution.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne value).2 levelAtValue
  have lowerLtQuantile : lower <
      distribution.lowerQuantile level positive atMostOne := by
    apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
    intro quantileLeLower
    have levelLeLower :=
      (distribution.lowerQuantile_le_iff_level_le_cumulative
        level positive atMostOne lower).1 quantileLeLower
    exact (not_le_of_gt belowLevel) levelLeLower
  rcases distribution.lowerQuantile_eq_positiveAtom_of_mem
      level positive atMostOne with
    ⟨atom, member, _weightPositive, valueEqual⟩
  have valueLeQuantile : value ≤
      distribution.lowerQuantile level positive atMostOne := by
    rcases gap atom member with atomLow | atomHigh
    · rw [valueEqual] at atomLow
      exact (not_le_of_gt lowerLtQuantile atomLow).elim
    · simpa only [valueEqual] using atomHigh
  exact Fraction.Order.Basic.Compatibility.le_antisymm _ _ quantileLeValue
    valueLeQuantile

end

namespace EvaluationEquivalent
end EvaluationEquivalent
end Distribution

end Purelib.Measure

end

end
