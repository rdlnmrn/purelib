module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.CauchySchwarz
public import Purelib.Measure.Distribution.Conditioning.Covariance.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Partition.Expectation
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite law of total covariance

For a displayed positive event partition, exact covariance splits into the
weighted within-cell conditional covariances and the covariance of the
displayed conditional means.  The proof is finite linearity over the listed
partition cells.
-/

namespace Purelib.Measure

namespace PositiveEventPartition

section
open Purelib
open Purelib.Data.Rat
/-- On a retained sublist of partition cells, weighted conditional covariance and mean-offset products equal the
corresponding centered-product event integrals. -/
private theorem weightedConditionalCovariances_eq_eventIntegrals
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event =>
          distribution.probability event *
            (distribution.conditionalCovariance event left right +
              (distribution.conditionalMean event left -
                distribution.expectation left) *
              (distribution.conditionalMean event right -
                distribution.expectation right))).sum =
        (events.map fun event =>
          distribution.eventIntegral event (fun item =>
            (left item - distribution.expectation left) *
              (right item - distribution.expectation right))).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      have eventMember : event ∈ partition.events :=
        subset event List.mem_cons_self
      have remainingSubset : ∀ candidate, candidate ∈ remaining →
          candidate ∈ partition.events :=
        fun candidate member =>
          subset candidate (List.mem_cons_of_mem event member)
      simp only [List.map_cons, List.sum_cons]
      rw [← distribution.conditionalMean_centeredProduct event
        (partition.positive event eventMember) left right]
      rw [distribution.probability_mul_conditionalMean event
        (fun item =>
          (left item - distribution.expectation left) *
            (right item - distribution.expectation right))
        (partition.positive event eventMember)]
      rw [weightedConditionalCovariances_eq_eventIntegrals
        partition left right remaining remainingSubset]

/-- The original covariance is the sum over positive cells of their probabilities times conditional covariance plus the
two conditional-mean offsets' product. -/
theorem total_covariance {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalCovariance event left right +
            (distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum =
      distribution.covariance left right := by
  rw [weightedConditionalCovariances_eq_eventIntegrals partition left right
    partition.events (fun event member => member)]
  unfold Distribution.covariance
  exact partition.toEventPartition.total_expectation fun item =>
    (left item - distribution.expectation left) *
      (right item - distribution.expectation right)

/-- When every retained cell has zero conditional covariance, the original covariance is the probability-weighted sum of
conditional-mean offset products. -/
theorem covariance_eq_between_of_conditionalCovariance_eq_zero
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational)
    (zero : ∀ event, event ∈ partition.events →
      distribution.conditionalCovariance event left right = 0) :
    distribution.covariance left right =
      (partition.events.map fun event =>
        distribution.probability event *
          ((distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum := by
  have removeWithin : ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event =>
        distribution.probability event *
          (distribution.conditionalCovariance event left right +
            (distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum =
      (events.map fun event =>
        distribution.probability event *
          ((distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum := by
    intro events subset
    induction events with
    | nil => rfl
    | cons event remaining inductionHypothesis =>
        have eventMember : event ∈ partition.events :=
          subset event List.mem_cons_self
        have remainingSubset : ∀ candidate, candidate ∈ remaining →
            candidate ∈ partition.events :=
          fun candidate member =>
            subset candidate (List.mem_cons_of_mem event member)
        simp only [List.map_cons, List.sum_cons, zero event eventMember,
          zero_add]
        rw [inductionHypothesis remainingSubset]
  rw [← partition.total_covariance left right]
  exact removeWithin partition.events (fun event member => member)

/-- The two partition conditional expectations have zero conditional covariance on every retained cell. -/
theorem conditionalCovariance_conditionalExpectations_eq_zero
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.conditionalCovariance event
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) = 0 := by
  have upper := distribution.conditionalCovariance_sq_le_variance_mul
    event (partition.positive event eventMember)
    (partition.conditionalExpectation left)
    (partition.conditionalExpectation right)
  rw [partition.conditionalVariance_conditionalExpectation_eq_zero
      left event eventMember,
    partition.conditionalVariance_conditionalExpectation_eq_zero
      right event eventMember,
    zero_mul] at upper
  have nonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct
    (distribution.conditionalCovariance event
      (partition.conditionalExpectation left)
      (partition.conditionalExpectation right))
  have squareZero := le_antisymm upper nonnegative
  exact Fraction.Order.Arithmetic.sq_eq_zero_direct _ |>.mp squareZero

/-- Replacing both observables by their partition conditional expectations preserves the retained between-cell
covariance terms. -/
private theorem betweenTerms_conditionalExpectations
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event =>
        distribution.probability event *
          ((distribution.conditionalMean event
              (partition.conditionalExpectation left) -
            distribution.expectation left) *
          (distribution.conditionalMean event
              (partition.conditionalExpectation right) -
            distribution.expectation right))).sum =
      (events.map fun event =>
        distribution.probability event *
          ((distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      have eventMember : event ∈ partition.events :=
        subset event List.mem_cons_self
      have remainingSubset : ∀ candidate, candidate ∈ remaining →
          candidate ∈ partition.events :=
        fun candidate member =>
          subset candidate (List.mem_cons_of_mem event member)
      simp only [List.map_cons, List.sum_cons]
      rw [partition.conditionalMean_conditionalExpectation
          left event eventMember,
        partition.conditionalMean_conditionalExpectation
          right event eventMember,
        betweenTerms_conditionalExpectations partition left right remaining
          remainingSubset]

/-- The covariance of partition conditional expectations equals the original probability-weighted between-cell
mean-offset product sum. -/
theorem covariance_conditionalExpectations_eq_between
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    distribution.covariance
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) =
      (partition.events.map fun event =>
        distribution.probability event *
          ((distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum := by
  rw [partition.covariance_eq_between_of_conditionalCovariance_eq_zero
    (partition.conditionalExpectation left)
    (partition.conditionalExpectation right)
    (partition.conditionalCovariance_conditionalExpectations_eq_zero
      left right)]
  rw [partition.expectation_conditionalExpectation left,
    partition.expectation_conditionalExpectation right]
  exact betweenTerms_conditionalExpectations partition left right
    partition.events (fun event member => member)

/-- Split the exact finite total-covariance sum into within-cell covariance and between-cell mean-offset product sums.
-/
private theorem totalCovarianceTerms_split
    {α : Type} (distribution : Measure.Distribution α)
    (left right : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (events.map fun event =>
        distribution.probability event *
          (distribution.conditionalCovariance event left right +
            (distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum =
      (events.map fun event =>
        distribution.probability event *
          distribution.conditionalCovariance event left right).sum +
      (events.map fun event =>
        distribution.probability event *
          ((distribution.conditionalMean event left -
              distribution.expectation left) *
            (distribution.conditionalMean event right -
              distribution.expectation right))).sum
  | [] => by
      simp only [List.map_nil, List.sum_nil]
      ring1
  | event :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      rw [totalCovarianceTerms_split distribution left right remaining]
      ring1

/-- The original covariance is the weighted conditional covariance sum plus the covariance of the two partition
conditional expectations. -/
theorem total_covariance_decomposition
    {α : Type} {distribution : Measure.Distribution α}
    (partition : Measure.PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          distribution.conditionalCovariance event left right).sum +
      distribution.covariance
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) =
      distribution.covariance left right := by
  rw [partition.covariance_conditionalExpectations_eq_between left right]
  rw [← totalCovarianceTerms_split distribution left right partition.events]
  exact partition.total_covariance left right

end

end PositiveEventPartition

end Purelib.Measure

end
