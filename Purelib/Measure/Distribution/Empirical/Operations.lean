module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Counting
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Normalization.Basic
public import Purelib.Measure.Content.Normalization.Operations
import Purelib.Measure.Content.Operations
public import Purelib.Measure.Distribution.Empirical.Basic
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Sampling.Statistic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Basic

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

/-- The original empirical law is evaluation-equivalent to normalization of the same exact counting-content list. -/
theorem empiricalDistribution_evaluationEquivalent_normalizedCounting
    {α : Type} (samples : List α) (positiveLength : 0 < samples.length)
    (positiveTotal : 0 < (countingContent samples).total) :
    Distribution.EvaluationEquivalent
      (empiricalDistribution samples positiveLength)
      ((countingContent samples).normalize positiveTotal) where
  probability_eq event := by
    rw [empiricalDistribution_probability,
      Content.normalize_probability,
      countingContent_measure, countingContent_total]
  expectation_eq value := by
    rw [empiricalDistribution_expectation,
      Content.normalize_expectation,
      countingContent_integral, countingContent_total]

open Purelib in
open Purelib.Data in
/-- Mapping the original empirical law is evaluation-equivalent to the empirical law of the exact mapped sample list. -/
theorem empiricalDistribution_map_evaluationEquivalent
    {α β : Type} (samples : List α) (positiveLength : 0 < samples.length)
    (function : α → β) :
    Distribution.EvaluationEquivalent
      ((empiricalDistribution samples positiveLength).map function)
      (empiricalDistribution (samples.map function) (by
        simpa only [List.Map.length_map] using positiveLength)) where
  probability_eq event := by
    rw [Distribution.map_probability,
      empiricalDistribution_probability,
      empiricalDistribution_probability,
      Data.List.countEvent_map]
    simp only [-eq_self, -iff_self, List.Map.length_map]
    rfl
  expectation_eq value := by
    rw [Distribution.map_expectation,
      empiricalDistribution_expectation,
      empiricalDistribution_expectation,
      sumValues_map]
    simp only [-eq_self, -iff_self, List.Map.length_map]
    rfl

open Purelib.Data.Rat in
open Purelib.Data in
/-- The empirical law of two nonempty appended samples is evaluation-equivalent to their length-weighted mixture. -/
theorem empiricalDistribution_append_evaluationEquivalent
    {α : Type} (left right : List α)
    (leftPositive : 0 < left.length) (rightPositive : 0 < right.length) :
    Distribution.EvaluationEquivalent
      (empiricalDistribution (left ++ right) (by
        simp only [List.Append.length_append]
        omega))
      ((empiricalDistribution left leftPositive).mixture
        (empiricalDistribution right rightPositive)
        (Content.appendMixingWeight
          (countingContent left) (countingContent right) (by
            rw [countingContent_total, countingContent_total]
            simpa only [zero_add] using
              Fraction.Order.Arithmetic.add_lt_add_direct
                (Fraction.Cast.Order.natCast_pos_direct leftPositive)
                (Fraction.Cast.Order.natCast_pos_direct
                  rightPositive)))) := by
  have leftTotalPositive : 0 < (countingContent left).total := by
    rw [countingContent_total]
    exact Fraction.Cast.Order.natCast_pos_direct leftPositive
  have rightTotalPositive : 0 < (countingContent right).total := by
    rw [countingContent_total]
    exact Fraction.Cast.Order.natCast_pos_direct rightPositive
  have sumTotalPositive :
      0 < (countingContent left).total + (countingContent right).total := by
    simpa only [zero_add] using
      Fraction.Order.Arithmetic.add_lt_add_direct
        leftTotalPositive rightTotalPositive
  have appendLengthPositive : 0 < (left ++ right).length := by
    simp only [List.Append.length_append]
    omega
  have appendTotalPositive :
      0 < (countingContent (left ++ right)).total := by
    rw [countingContent_total]
    exact Fraction.Cast.Order.natCast_pos_direct appendLengthPositive
  have empiricalToCountingRaw :=
    empiricalDistribution_evaluationEquivalent_normalizedCounting
      (left ++ right) appendLengthPositive appendTotalPositive
  have empiricalToCounting :
      Distribution.EvaluationEquivalent
        (empiricalDistribution (left ++ right) appendLengthPositive)
        (((countingContent left).append (countingContent right)).normalize
          (by
            rw [Content.append_total]
            exact sumTotalPositive)) := by
    simpa only [countingContent_append] using empiricalToCountingRaw
  have appendToMixture :=
    Content.append_normalize_evaluationEquivalent
      (countingContent left) (countingContent right)
      leftTotalPositive rightTotalPositive
  have components :=
    (empiricalDistribution_evaluationEquivalent_normalizedCounting
      left leftPositive leftTotalPositive).symm.mixture
      (empiricalDistribution_evaluationEquivalent_normalizedCounting
        right rightPositive rightTotalPositive).symm
      (Content.appendMixingWeight
        (countingContent left) (countingContent right)
        sumTotalPositive)
  exact (empiricalToCounting.trans appendToMixture).trans components

section
open Purelib.Data.Rat
/-- Retain the certified mixing weight computed from the lengths of the two original nonempty sample lists. -/
def empiricalAppendWeight {α : Type} (left right : List α)
    (leftPositive : 0 < left.length) (rightPositive : 0 < right.length) :
    MixingWeight :=
  Content.appendMixingWeight
    (countingContent left) (countingContent right) (by
      rw [countingContent_total, countingContent_total]
      simpa only [zero_add] using
        Fraction.Order.Arithmetic.add_lt_add_direct
          (Fraction.Cast.Order.natCast_pos_direct leftPositive)
          (Fraction.Cast.Order.natCast_pos_direct rightPositive))

/-- The exact empirical append coefficient is the left length divided by the sum of original lengths. -/
theorem empiricalAppendWeight_coefficient {α : Type}
    (left right : List α) (leftPositive : 0 < left.length)
    (rightPositive : 0 < right.length) :
    (empiricalAppendWeight left right leftPositive rightPositive).coefficient =
      (left.length : Fraction.Rational) /
        ((left.length : Fraction.Rational) + (right.length : Fraction.Rational)) := by
  unfold empiricalAppendWeight Content.appendMixingWeight
  change (countingContent left).total /
      ((countingContent left).total + (countingContent right).total) = _
  rw [countingContent_total, countingContent_total]

end

/-- Appending the original nonempty samples gives a law evaluation-equivalent to their mixture with the exact retained
append weight. -/
theorem empiricalDistribution_append_mixture {α : Type}
    (left right : List α) (leftPositive : 0 < left.length)
    (rightPositive : 0 < right.length) :
    Distribution.EvaluationEquivalent
      (empiricalDistribution (left ++ right) (by
        simp only [List.length_append]
        omega))
      ((empiricalDistribution left leftPositive).mixture
        (empiricalDistribution right rightPositive)
        (empiricalAppendWeight left right leftPositive rightPositive)) := by
  unfold empiricalAppendWeight
  exact empiricalDistribution_append_evaluationEquivalent
    left right leftPositive rightPositive
end Purelib.Measure

end
