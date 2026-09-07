import FiniteMeasure.IndependentMoments
import FiniteMeasure.DistributionEquivalence

/-!
# Finite rational convolution

Convolution is the finite pushforward of an explicit product distribution by
rational addition.  Its event, expectation, and variance identities are
finite Fubini and independent-moment calculations.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact finite convolution of two rational-valued distributions. -/
def convolve (left right : Distribution Coordinate) :
    Distribution Coordinate :=
  (left.product right).map fun pair => pair.1 + pair.2

/-- Convolution probability as an exact finite iterated probability. -/
theorem convolve_probability (left right : Distribution Coordinate)
    (event : Coordinate → Bool) :
    (left.convolve right).probability event =
      left.expectation (fun leftValue =>
        right.probability (fun rightValue =>
          event (leftValue + rightValue))) := by
  rw [convolve, map_probability, product_probability_iterated]

/-- Convolution expectation as an exact finite double average. -/
theorem convolve_expectation_value
    (left right : Distribution Coordinate)
    (value : Coordinate → Coordinate) :
    (left.convolve right).expectation value =
      left.expectation (fun leftValue =>
        right.expectation (fun rightValue =>
          value (leftValue + rightValue))) := by
  rw [convolve, map_expectation, product_expectation_iterated]

/-- Finite rational convolution is commutative up to observational
equivalence of the two explicit atom-table layouts. -/
theorem convolve_comm_evaluationEquivalent
    (left right : Distribution Coordinate) :
    EvaluationEquivalent (left.convolve right) (right.convolve left) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [left.convolve_expectation_value right value,
    right.convolve_expectation_value left value]
  calc
    left.expectation (fun leftValue =>
          right.expectation (fun rightValue =>
            value (leftValue + rightValue))) =
        right.expectation (fun rightValue =>
          left.expectation (fun leftValue =>
            value (leftValue + rightValue))) :=
      left.expectation_exchange right
        (fun leftValue rightValue => value (leftValue + rightValue))
    _ = right.expectation (fun rightValue =>
          left.expectation (fun leftValue =>
            value (rightValue + leftValue))) := by
      exact right.expectation_congr _ _ (fun rightValue =>
        left.expectation_congr _ _ (fun leftValue => by rw [add_comm]))

/-- Pushforward transports finite variance by direct composition. -/
theorem map_variance {α β : Type} (source : Distribution α)
    (function : α → β) (value : β → Coordinate) :
    (source.map function).variance value =
      source.variance (fun item => value (function item)) := by
  rw [(source.map function).variance_eq_secondMoment_sub_sq,
    source.variance_eq_secondMoment_sub_sq,
    source.map_expectation function (fun item => value item ^ 2),
    source.map_expectation function value]

/-- The expectation of a finite rational convolution is the sum of the two
expectations. -/
theorem convolve_expectation (left right : Distribution Coordinate) :
    (left.convolve right).expectation (fun value => value) =
      left.expectation (fun value => value) +
        right.expectation (fun value => value) := by
  rw [convolve, map_expectation]
  change (left.product right).expectation
      (fun pair => pair.1 + pair.2) = _
  rw [(left.product right).expectation_add]
  exact congrArg₂ (fun leftMean rightMean => leftMean + rightMean)
    (left.product_expectation_left right (fun value => value))
    (left.product_expectation_right right (fun value => value))

/-- Independent finite rational convolution variances add exactly. -/
theorem convolve_variance (left right : Distribution Coordinate) :
    (left.convolve right).variance (fun value => value) =
      left.variance (fun value => value) +
        right.variance (fun value => value) := by
  rw [convolve, map_variance]
  exact left.product_variance_add_coordinates right
    (fun value => value) (fun value => value)

end Distribution

end FiniteMeasure
