import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConditionalCauchySchwarz
import FiniteMeasure.CovarianceAlgebra

/-!
# Finite law of total covariance

For a displayed positive event partition, exact covariance splits into the
weighted within-cell conditional covariances and the covariance of the
displayed conditional means.  The proof is finite linearity over the listed
partition cells.
-/

namespace FiniteMeasure

namespace Distribution

private theorem conditionalMean_centeredProduct {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    distribution.conditionalMean event (fun item =>
        (left item - distribution.expectation left) *
          (right item - distribution.expectation right)) =
      distribution.conditionalCovariance event left right +
        (distribution.conditionalMean event left -
          distribution.expectation left) *
        (distribution.conditionalMean event right -
          distribution.expectation right) := by
  let leftMean := distribution.expectation left
  let rightMean := distribution.expectation right
  rw [distribution.conditionalCovariance_eq_product_sub_mul
      event positive left right]
  change distribution.conditionalMean event (fun item =>
      (left item - leftMean) * (right item - rightMean)) = _
  calc
    distribution.conditionalMean event (fun item =>
          (left item - leftMean) * (right item - rightMean)) =
        distribution.conditionalMean event (fun item =>
          (left item * right item - leftMean * right item) -
            rightMean * left item + leftMean * rightMean) :=
      distribution.conditionalMean_congr event _ _
        (fun item => by ring1)
    _ = _ := by
      rw [distribution.conditionalMean_add,
        distribution.conditionalMean_sub,
        distribution.conditionalMean_sub,
        distribution.conditionalMean_scale,
        distribution.conditionalMean_scale,
        distribution.conditionalMean_constant event positive]
      dsimp only [leftMean, rightMean]
      ring1

end Distribution

namespace PositiveEventPartition

private theorem weightedConditionalCovariances_eq_eventIntegrals
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
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

/-- Exact finite law of total covariance. -/
theorem total_covariance {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
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

/-- When every displayed within-cell conditional covariance vanishes, the
between-cell mean shifts account for all covariance. -/
theorem covariance_eq_between_of_conditionalCovariance_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate)
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

/-- Two conditional-expectation observables have zero conditional covariance
inside every cell of their defining partition. -/
theorem conditionalCovariance_conditionalExpectations_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) (event : α → Bool)
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
  have nonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct
    (distribution.conditionalCovariance event
      (partition.conditionalExpectation left)
      (partition.conditionalExpectation right))
  have squareZero := le_antisymm upper nonnegative
  exact RFAP.ConstructiveFraction.sq_eq_zero_direct _ |>.mp squareZero

private theorem betweenTerms_conditionalExpectations
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
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

/-- The between-cell covariance is exactly the covariance of the two finite
conditional-expectation observables. -/
theorem covariance_conditionalExpectations_eq_between
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
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

private theorem totalCovarianceTerms_split
    {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
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

/-- Textbook finite law of total covariance: exact covariance is the sum of
the displayed within-cell conditional covariances and the covariance of the
two partition conditional expectations. -/
theorem total_covariance_decomposition
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
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

end PositiveEventPartition

end FiniteMeasure
