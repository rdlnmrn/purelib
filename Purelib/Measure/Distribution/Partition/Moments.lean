module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.Moments
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Moments.Basic
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Partition.Expectation

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

/-- A positive-probability event list's weighted conditional variances and mean displacements equal its
squared-deviation event integrals. -/
private theorem weightedConditionalVariances_eq_eventIntegrals
    {α : Type} (distribution : Measure.Distribution α)
    (value : α → Fraction.Rational) (center : Fraction.Rational) :
    ∀ (events : List (α → Bool)),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event =>
          distribution.probability event *
            (distribution.conditionalVariance event value +
              (distribution.conditionalMean event value - center) ^ 2)).sum =
        (events.map fun event =>
          distribution.eventIntegral event
            (fun item => (value item - center) ^ 2)).sum
  | [], positive => rfl
  | event :: remaining, positive => by
      simp only [List.map_cons, List.sum_cons]
      rw [← distribution.conditionalMean_sq_sub_center event
        (positive event List.mem_cons_self) value center]
      rw [distribution.probability_mul_conditionalMean event
        (fun item => (value item - center) ^ 2)
        (positive event List.mem_cons_self)]
      rw [weightedConditionalVariances_eq_eventIntegrals
        distribution value center remaining (fun candidate member =>
          positive candidate (List.mem_cons_of_mem event member))]

/-- The retained positive partition decomposes variance into probability-weighted conditional variances and squared
cell-mean displacements.

Every conditional reading uses the original distribution and exact displayed cell. The finite partition's
total-expectation identity recombines these readings. -/
theorem total_variance {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalVariance event value +
            (distribution.conditionalMean event value -
              distribution.expectation value) ^ 2)).sum =
      distribution.variance value := by
  rw [weightedConditionalVariances_eq_eventIntegrals distribution value
    (distribution.expectation value) partition.events partition.positive]
  change
    (partition.toEventPartition.events.map fun event =>
      distribution.eventIntegral event
        (fun item => (value item - distribution.expectation value) ^ 2)).sum =
      distribution.expectation
        (fun item => (value item - distribution.expectation value) ^ 2)
  exact partition.toEventPartition.total_expectation
    (fun item => (value item - distribution.expectation value) ^ 2)

/-- The variance terms of partition conditional expectation reduce to squared original cell-mean displacements. -/
private theorem conditionalExpectation_varianceTerms
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event => distribution.probability event *
        (distribution.conditionalVariance event
            (partition.conditionalExpectation value) +
          (distribution.conditionalMean event
              (partition.conditionalExpectation value) -
            distribution.expectation
              (partition.conditionalExpectation value)) ^ 2)).sum =
      (events.map fun event => distribution.probability event *
        (distribution.conditionalMean event value -
          distribution.expectation value) ^ 2).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [partition.conditionalVariance_conditionalExpectation_eq_zero
          value event (subset event List.mem_cons_self),
        partition.conditionalMean_conditionalExpectation value event
          (subset event List.mem_cons_self),
        conditionalExpectation_varianceTerms partition value remaining
          (fun candidate member =>
            subset candidate (List.mem_cons_of_mem event member)),
        partition.expectation_conditionalExpectation value]
      ring1

/-- Variance of partition conditional expectation equals the probability-weighted squared displacements of its cell
means from the original mean. -/
theorem variance_conditionalExpectation_eq_between {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    distribution.variance (partition.conditionalExpectation value) =
      (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalMean event value -
            distribution.expectation value) ^ 2).sum := by
  calc
    distribution.variance (partition.conditionalExpectation value) =
        (partition.events.map fun event =>
          distribution.probability event *
            (distribution.conditionalVariance event
                (partition.conditionalExpectation value) +
              (distribution.conditionalMean event
                  (partition.conditionalExpectation value) -
                distribution.expectation
                  (partition.conditionalExpectation value)) ^ 2)).sum :=
      (partition.total_variance
        (partition.conditionalExpectation value)).symm
    _ = (partition.events.map fun event =>
          distribution.probability event *
            (distribution.conditionalMean event value -
              distribution.expectation value) ^ 2).sum :=
      conditionalExpectation_varianceTerms partition value partition.events
        (fun event member => member)

/-- The weighted cell-mean displacement sum is bounded by the same sum with nonnegative conditional variances included.
-/
private theorem betweenVariance_le_totalVariance
    {α : Type} (distribution : Measure.Distribution α)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event => distribution.probability event *
        (distribution.conditionalMean event value -
          distribution.expectation value) ^ 2).sum ≤
      (events.map fun event => distribution.probability event *
        (distribution.conditionalVariance event value +
          (distribution.conditionalMean event value -
            distribution.expectation value) ^ 2)).sum
  | [], positive => le_rfl
  | event :: remaining, positive => by
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add
      · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact le_add_of_nonneg_left
            (distribution.conditionalVariance_nonneg event
              (positive event List.mem_cons_self) value)
        · exact distribution.probability_nonneg event
      · exact betweenVariance_le_totalVariance distribution value remaining
          (fun candidate member =>
            positive candidate (List.mem_cons_of_mem event member))

/-- Taking conditional expectation on the retained positive partition cannot increase variance. -/
theorem variance_conditionalExpectation_le {α : Type}
    {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    distribution.variance (partition.conditionalExpectation value) ≤
      distribution.variance value := by
  rw [partition.variance_conditionalExpectation_eq_between value,
    ← partition.total_variance value]
  exact betweenVariance_le_totalVariance distribution value partition.events
    partition.positive

end PositiveEventPartition

end Purelib.Measure

end
section
/-!
# Finite laws of total second moment and variance

The usual conditional moment decompositions are exact rational identities
over an explicitly displayed positive event partition.  Every conditional
mean and variance is computed from finite weighted lists.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

/-- Split the finite weighted variance sum into its conditional-variance and cell-mean displacement sums. -/
private theorem totalVarianceTerms_split
    {α : Type} (distribution : Measure.Distribution α)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (events.map fun event =>
        distribution.probability event *
          (distribution.conditionalVariance event value +
            (distribution.conditionalMean event value -
              distribution.expectation value) ^ 2)).sum =
      (events.map fun event =>
        distribution.probability event *
          distribution.conditionalVariance event value).sum +
      (events.map fun event =>
        distribution.probability event *
          (distribution.conditionalMean event value -
            distribution.expectation value) ^ 2).sum
  | [] => by
      simp only [List.map_nil, List.sum_nil]
      ring1
  | event :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      rw [totalVarianceTerms_split distribution value remaining]
      ring1

/-- Original variance equals expected conditional variance plus variance of the retained partition conditional
expectation. -/
theorem total_variance_decomposition
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          distribution.conditionalVariance event value).sum +
      distribution.variance (partition.conditionalExpectation value) =
      distribution.variance value := by
  rw [partition.variance_conditionalExpectation_eq_between value]
  rw [← totalVarianceTerms_split distribution value partition.events]
  exact partition.total_variance value

/-- For a finite positive-probability event list, conditional variance plus squared conditional mean reconstructs each
conditional second moment. -/
private theorem weightedConditionalSecondMoments
    {α : Type} (distribution : Measure.Distribution α)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event =>
        distribution.probability event *
          (distribution.conditionalVariance event value +
            distribution.conditionalMean event value ^ 2)).sum =
      (events.map fun event =>
        distribution.probability event *
          distribution.conditionalMean event
            (fun item => value item ^ 2)).sum
  | [], positive => rfl
  | event :: remaining, positive => by
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.conditionalVariance_eq_secondMoment_sub_sq event
          (positive event List.mem_cons_self) value,
        weightedConditionalSecondMoments distribution value remaining
          (fun candidate member =>
            positive candidate (List.mem_cons_of_mem event member))]
      ring1

/-- The weighted conditional variances and squared conditional means over the partition recover the original second
moment. -/
theorem total_secondMoment
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalVariance event value +
            distribution.conditionalMean event value ^ 2)).sum =
      distribution.expectation (fun item => value item ^ 2) := by
  rw [weightedConditionalSecondMoments distribution value partition.events
    partition.positive]
  exact partition.total_expectation fun item => value item ^ 2

/-- Expected conditional variance plus the second moment of partition conditional expectation equals the original second
moment. -/
theorem expectedConditionalVariance_add_conditionalExpectation_secondMoment
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          distribution.conditionalVariance event value).sum +
      distribution.expectation (fun item =>
        partition.conditionalExpectation value item ^ 2) =
      distribution.expectation (fun item => value item ^ 2) := by
  have decomposition := partition.total_variance_decomposition value
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    partition.expectation_conditionalExpectation value] at decomposition
  calc
    (partition.events.map fun event =>
          distribution.probability event *
            distribution.conditionalVariance event value).sum +
        distribution.expectation (fun item =>
          partition.conditionalExpectation value item ^ 2) =
      ((partition.events.map fun event =>
          distribution.probability event *
            distribution.conditionalVariance event value).sum +
        (distribution.expectation (fun item =>
            partition.conditionalExpectation value item ^ 2) -
          distribution.expectation value ^ 2)) +
        distribution.expectation value ^ 2 := by ring1
    _ = (distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2) +
        distribution.expectation value ^ 2 := by
      rw [decomposition]
    _ = distribution.expectation (fun item => value item ^ 2) := by ring1

end PositiveEventPartition

end Purelib.Measure

end

