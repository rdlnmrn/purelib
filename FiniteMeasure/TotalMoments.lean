import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments
import FiniteMeasure.PartitionExpectation

/-!
# Finite laws of total second moment and variance

The usual conditional moment decompositions are exact rational identities
over an explicitly displayed positive event partition.  Every conditional
mean and variance is computed from finite weighted lists.
-/

namespace FiniteMeasure

namespace PositiveEventPartition

private theorem totalVarianceTerms_split
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
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

/-- Textbook finite law of total variance: within-cell conditional variance
plus variance of the finite conditional expectation equals total variance. -/
theorem total_variance_decomposition
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    (partition.events.map fun event =>
        distribution.probability event *
          distribution.conditionalVariance event value).sum +
      distribution.variance (partition.conditionalExpectation value) =
      distribution.variance value := by
  rw [partition.variance_conditionalExpectation_eq_between value]
  rw [← totalVarianceTerms_split distribution value partition.events]
  exact partition.total_variance value

private theorem weightedConditionalSecondMoments
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
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

/-- Exact finite conditional second-moment identity. -/
theorem total_secondMoment
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalVariance event value +
            distribution.conditionalMean event value ^ 2)).sum =
      distribution.expectation (fun item => value item ^ 2) := by
  rw [weightedConditionalSecondMoments distribution value partition.events
    partition.positive]
  exact partition.total_expectation fun item => value item ^ 2

/-- Expected within-cell conditional variance plus the second moment of the
finite conditional expectation equals the original second moment. -/
theorem expectedConditionalVariance_add_conditionalExpectation_secondMoment
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
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

end FiniteMeasure
