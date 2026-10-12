module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Multiplicity
public import Purelib.Examples.Measure.Content.Counting.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
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
import Purelib.Measure.Distribution.Empirical.Basic
public import Purelib.Measure.Distribution.Empirical.Histogram
import Purelib.Measure.Sampling.Statistic
public import Purelib.Measure.Content.Counting
import Purelib.Measure.Content.Normalization.Operations
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Empirical.Operations
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Empirical.Moments
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Empirical.EssentialMaximum
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Content.Normalization.Basic
import Purelib.Measure.Distribution.Lp.Equivalence
import Purelib.Measure.Distribution.Empirical.Lp
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Empirical.WorkedExamples

open Purelib
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Content.Counting.WorkedExamples (observedEven observedRolls)

/-- The empirical distribution of the retained roll list `[1, 2, 2, 4]`. -/
def observedDistribution : Distribution Nat :=
  empiricalDistribution observedRolls (by decide)

/-- The early roll sublist `[1, 2]`. -/
def earlyRolls : List Nat := [1, 2]

/-- The late roll sublist `[2, 4]`. -/
def lateRolls : List Nat := [2, 4]

/-- The full empirical law is evaluation-equivalent to the mass-weighted mixture of its two retained sublists. -/
example : Distribution.EvaluationEquivalent observedDistribution
    ((empiricalDistribution earlyRolls (by decide)).mixture
      (empiricalDistribution lateRolls (by decide))
      (Content.appendMixingWeight
        (countingContent earlyRolls) (countingContent
          lateRolls)
        (by decide))) := by
  unfold observedDistribution
    observedRolls earlyRolls
    lateRolls
  exact empiricalDistribution_append_evaluationEquivalent
    [1, 2] [2, 4] (by decide) (by decide)

/-- The empirical distribution with repeated equal atom payloads consolidated. -/
def consolidatedObservedDistribution :
  Distribution Nat :=
  observedDistribution.consolidate

/-- The frequency histogram of the original retained roll list. -/
def observedHistogram : Distribution Nat :=
  empiricalHistogram observedRolls (by decide)

/-- The histogram's rational coordinate has powered L2 value `25/4`. -/
example : observedHistogram.poweredL2
    (fun value : Nat => (value : Fraction.Rational)) = 25 / 4 := by
  calc
    observedHistogram.poweredL2
        (fun value : Nat => (value : Fraction.Rational)) =
      observedDistribution.poweredL2
        (fun value : Nat => (value : Fraction.Rational)) :=
      Distribution.EvaluationEquivalent.poweredL2_eq
        (empiricalHistogram_evaluationEquivalent observedRolls (by decide))
        (fun value : Nat => (value : Fraction.Rational))
    _ = 25 / 4 := by decide

/-- The histogram's coordinate has essential maximum magnitude four. -/
example : observedHistogram.essentialMaximumMagnitude
    (fun value : Nat => (value : Fraction.Rational)) = 4 := by
  unfold observedHistogram
    observedRolls
  rw [empiricalHistogram_essentialMaximumMagnitude]
  decide

/-- Consolidation leaves three distinct atom payloads. -/
example : consolidatedObservedDistribution.atoms.length = 3 := by
  decide

/-- The empirical histogram has three atoms. -/
example : observedHistogram.atoms.length = 3 := by
  decide

/-- The histogram has no repeated atom payloads. -/
example : NoRepeatedPayloads observedHistogram.atoms := by
  unfold observedHistogram
  exact empiricalHistogram_noRepeatedPayloads observedRolls (by decide)

/-- The empirical distribution gives observation two mass one half. -/
example : observedDistribution.atomMass 2 = 1 / 2 := by
  decide

/-- The original sample list contains two occurrences of observation two. -/
example : Purelib.Data.List.countItem observedRolls 2 = 2 := by
  decide

/-- Every candidate observation is either present in or absent from the retained finite sample list. -/
example (item : Nat) :
    Purelib.Data.List.SampleContains item observedRolls ∨
      Purelib.Data.List.SampleAbsent item observedRolls :=
  Data.List.sampleContains_or_sampleAbsent item observedRolls

/-- Observation two has positive empirical mass because it occurs in the original sample. -/
example : 0 < observedDistribution.atomMass 2 := open Purelib in by
  unfold observedDistribution
  apply empiricalDistribution_atomMass_pos_of_sampleContains
  simp [observedRolls, Data.List.SampleContains]

/-- The histogram gives observation two mass one half. -/
example : observedHistogram.atomMass 2 = 1 / 2 := by
  unfold observedHistogram
  rw [empiricalHistogram_atomMass_eq_countItem]
  decide

/-- The absent observation three has empirical mass zero. -/
example : observedDistribution.atomMass 3 = 0 := open Purelib in by
  unfold observedDistribution
  exact empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
    observedRolls (by decide) 3 (by
      simp [observedRolls, Data.List.SampleAbsent])

/-- Consolidation preserves the mass one half at observation two. -/
example : consolidatedObservedDistribution.atomMass 2 = 1 / 2 := by
  decide

/-- The consolidated and original empirical distributions are evaluation-equivalent. -/
example : Distribution.EvaluationEquivalent
    consolidatedObservedDistribution
      observedDistribution := by
  unfold consolidatedObservedDistribution
  exact observedDistribution.consolidate_evaluationEquivalent

/-- Consolidation preserves the original empirical coordinate variance. -/
example : consolidatedObservedDistribution.variance
      (fun value : Nat => (value : Fraction.Rational)) =
    observedDistribution.variance
      (fun value : Nat => (value : Fraction.Rational)) :=
  observedDistribution.consolidate_evaluationEquivalent.variance_eq
    (fun value : Nat => (value : Fraction.Rational))

/-- The observed even-event probability is three quarters. -/
example : observedDistribution.probability
  observedEven = 3 / 4 := by
  decide

/-- The empirical even-event probability equals its frequency in the original sample list. -/
example : observedDistribution.probability
  observedEven =
    Distribution.eventFrequency observedRolls.length
      observedEven
      observedRolls := by
  unfold observedDistribution
  exact empiricalDistribution_probability_eq_eventFrequency observedRolls
    (by decide) observedEven

/-- The empirical rational-coordinate expectation is `9/4`. -/
example : observedDistribution.expectation
    (fun value => (value : Fraction.Rational)) = 9 / 4 := by
  decide

/-- The empirical rational coordinate has powered L2 value `25/4`. -/
example : observedDistribution.poweredL2
    (fun value : Nat => (value : Fraction.Rational)) = 25 / 4 := by
  unfold observedDistribution
    observedRolls
  rw [empiricalDistribution_poweredL2]
  decide

/-- The empirical coordinate has essential maximum magnitude four. -/
example : observedDistribution.essentialMaximumMagnitude
    (fun value : Nat => (value : Fraction.Rational)) = 4 := by
  unfold observedDistribution
    observedRolls
  rw [empiricalDistribution_essentialMaximumMagnitude]
  decide

/-- The coordinate's essential maximum distance from the constant two is two. -/
example : observedDistribution.essentialMaximumDistance
    (fun value : Nat => (value : Fraction.Rational)) (fun _ => 2) = 2 := by
  unfold observedDistribution
    observedRolls
  rw [empiricalDistribution_essentialMaximumDistance]
  decide

/-- The empirical expectation equals the original finite sample mean. -/
example : observedDistribution.expectation
      (fun value : Nat => (value : Fraction.Rational)) =
    Distribution.sampleMean observedRolls.length
      (fun value : Nat => (value : Fraction.Rational)) observedRolls :=
  empiricalDistribution_expectation_eq_sampleMean observedRolls
    (by decide) (fun value : Nat => (value : Fraction.Rational))

/-- Mapping the empirical law through the even event agrees with the empirical law of the mapped original sample. -/
example : Distribution.EvaluationEquivalent
    (observedDistribution.map
      observedEven)
    (empiricalDistribution (observedRolls.map
      observedEven) (by decide)) := by
  unfold observedDistribution
  exact empiricalDistribution_map_evaluationEquivalent
    observedRolls (by decide)
      observedEven

/-- The empirical variance equals the sample mean of squared deviations from `9/4`. -/
example : observedDistribution.variance
      (fun value : Nat => (value : Fraction.Rational)) =
    Distribution.sampleMean observedRolls.length
      (fun value : Nat =>
        ((value : Fraction.Rational) - 9 / 4) ^ 2) observedRolls := by
  unfold observedDistribution
  rw [empiricalDistribution_variance_eq_sampleMean]
  decide

/-- The empirical coordinate variance is `19/16`. -/
example : observedDistribution.variance
    (fun value : Nat => (value : Fraction.Rational)) = 19 / 16 := by
  decide

/-- The full empirical variance decomposes into the two retained sublist variances and their weighted squared mean gap.
-/
example : observedDistribution.variance
      (fun value : Nat => (value : Fraction.Rational)) =
    let weight := empiricalAppendWeight earlyRolls
      lateRolls
      (by decide) (by decide)
    weight.coefficient *
        (empiricalDistribution earlyRolls (by decide)).variance
          (fun value : Nat => (value : Fraction.Rational)) +
      weight.complement *
        (empiricalDistribution lateRolls (by decide)).variance
          (fun value : Nat => (value : Fraction.Rational)) +
      weight.coefficient * weight.complement *
        ((empiricalDistribution earlyRolls (by decide)).expectation
            (fun value : Nat => (value : Fraction.Rational)) -
          (empiricalDistribution lateRolls (by decide)).expectation
            (fun value : Nat => (value : Fraction.Rational))) ^ 2 := by
  unfold observedDistribution
    observedRolls earlyRolls
    lateRolls
  exact empiricalDistribution_append_variance
    [1, 2] [2, 4] (by decide) (by decide)
      (fun value : Nat => (value : Fraction.Rational))

/-- The distribution obtained by normalizing the original counting content. -/
def normalizedObservedContent : Distribution Nat
  :=
  (countingContent observedRolls).normalize (by decide)

/-- The original empirical law is evaluation-equivalent to normalized counting content. -/
example : Distribution.EvaluationEquivalent observedDistribution
    normalizedObservedContent := by
  unfold observedDistribution
    normalizedObservedContent
  exact empiricalDistribution_evaluationEquivalent_normalizedCounting
    observedRolls (by decide) (by decide)

/-- Mapping and normalizing the original counting content commute up to evaluation equivalence. -/
example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).map
      observedEven).normalize (by decide))
    (normalizedObservedContent.map
      observedEven) := by
  unfold normalizedObservedContent
  exact (countingContent observedRolls).map_normalize_evaluationEquivalent
    (by decide) observedEven

/-- Normalizing the positive even restriction agrees with conditioning the normalized original content. -/
example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).restrict
      observedEven).normalize
      (by decide))
    (normalizedObservedContent.conditioned
      observedEven (by decide)) := by
  unfold normalizedObservedContent
  exact Content.restrict_normalize_evaluationEquivalent
    (countingContent observedRolls) (by decide)
      observedEven (by decide)

/-- Normalizing the product counting content agrees with the product of the normalized distributions. -/
example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).product
      (countingContent observedRolls)).normalize (by decide))
    (normalizedObservedContent.product
      normalizedObservedContent) := by
  unfold normalizedObservedContent
  exact Content.product_normalize_evaluationEquivalent
    (countingContent observedRolls) (countingContent
      observedRolls)
      (by decide) (by decide)

/-- Appending the counting content to itself gives mixing coefficient one half. -/
example :
    (Content.appendMixingWeight
      (countingContent observedRolls) (countingContent
        observedRolls)
      (by decide)).coefficient = 1 / 2 := by
  decide

/-- Normalizing the appended content agrees with its mass-weighted mixture of normalized laws. -/
example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).append
      (countingContent observedRolls)).normalize (by decide))
    (normalizedObservedContent.mixture
      normalizedObservedContent
      (Content.appendMixingWeight
        (countingContent observedRolls) (countingContent
          observedRolls)
        (by decide))) := by
  unfold normalizedObservedContent
  exact Content.append_normalize_evaluationEquivalent
    (countingContent observedRolls) (countingContent
      observedRolls)
      (by decide) (by decide)

/-- The normalized counting content assigns the even event probability three quarters. -/
example : normalizedObservedContent.probability
  observedEven = 3 / 4 := by
  decide

/-- The normalized coordinate expectation equals the original integral divided by total content. -/
example : normalizedObservedContent.expectation
    (fun value => (value : Fraction.Rational)) =
      (countingContent observedRolls).integral
          (fun value => (value : Fraction.Rational)) /
        (countingContent observedRolls).total :=
  (countingContent observedRolls).normalize_expectation (by decide)
    (fun value => (value : Fraction.Rational))

end Purelib.Examples.Measure.Distribution.Empirical.WorkedExamples

end
