import FiniteMeasure.ConditionalCauchySchwarz
import FiniteMeasure.OneSidedMoments

/-!
# Conditional finite moment inequalities

An explicitly positive conditioning event produces a displayed rational
distribution.  Its expectation, variance, and event probabilities are the
corresponding conditional quantities on the source table.  The ordinary
finite Markov, Chebyshev, and Cantelli inequalities therefore transport
directly, with all hypotheses remaining pointwise and executable.
-/

namespace FiniteMeasure

namespace Distribution

/-- Variance under the explicitly conditioned law is exactly conditional
variance on the source distribution. -/
theorem conditioned_variance_eq_conditionalVariance {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Coordinate) :
    (distribution.conditioned condition conditionPositive).variance value =
      distribution.conditionalVariance condition value := by
  unfold variance varianceAround conditionalVariance
  rw [distribution.conditioned_expectation_eq_conditionalMean
      condition conditionPositive value,
    distribution.conditioned_expectation_eq_conditionalMean
      condition conditionPositive]

/-- Conditional Markov inequality on one positive conditioning event. -/
theorem conditionalMarkov_bound {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Coordinate) (threshold : Coordinate)
    (thresholdPositive : 0 < threshold)
    (nonnegative : ∀ item, 0 ≤ value item)
    (selectedLower : ∀ item, event item = true → threshold ≤ value item) :
    distribution.conditionalProbability event condition conditionPositive ≤
      distribution.conditionalMean condition value / threshold := by
  have bound := (distribution.conditioned condition conditionPositive)
    |>.markov_bound event value threshold thresholdPositive
      (fun atom member => nonnegative atom.item)
      (fun atom member selected => selectedLower atom.item selected)
  rw [distribution.conditioned_probability condition event conditionPositive,
    distribution.conditioned_expectation_eq_conditionalMean
      condition conditionPositive value] at bound
  exact bound

/-- Conditional Chebyshev inequality around the exact rational conditional
mean. -/
theorem conditionalChebyshev_bound {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Coordinate) (threshold : Coordinate)
    (thresholdPositive : 0 < threshold)
    (selectedDeviation : ∀ item, event item = true →
      threshold ^ 2 ≤
        (value item - distribution.conditionalMean condition value) ^ 2) :
    distribution.conditionalProbability event condition conditionPositive ≤
      distribution.conditionalVariance condition value / threshold ^ 2 := by
  have bound := (distribution.conditioned condition conditionPositive)
    |>.chebyshev_bound event value threshold thresholdPositive (by
      intro atom member selected
      rw [distribution.conditioned_expectation_eq_conditionalMean
        condition conditionPositive value]
      exact selectedDeviation atom.item selected)
  rw [distribution.conditioned_probability condition event conditionPositive,
    distribution.conditioned_variance_eq_conditionalVariance
      condition conditionPositive value] at bound
  exact bound

/-- Conditional upper-tail Cantelli inequality. -/
theorem conditionalCantelli_bound {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Coordinate) (threshold : Coordinate)
    (thresholdPositive : 0 < threshold)
    (selectedDeviation : ∀ item, event item = true →
      threshold ≤ value item -
        distribution.conditionalMean condition value) :
    distribution.conditionalProbability event condition conditionPositive ≤
      distribution.conditionalVariance condition value /
        (distribution.conditionalVariance condition value + threshold ^ 2) := by
  have bound := (distribution.conditioned condition conditionPositive)
    |>.cantelli_bound event value threshold thresholdPositive (by
      intro atom member selected
      rw [distribution.conditioned_expectation_eq_conditionalMean
        condition conditionPositive value]
      exact selectedDeviation atom.item selected)
  rw [distribution.conditioned_probability condition event conditionPositive,
    distribution.conditioned_variance_eq_conditionalVariance
      condition conditionPositive value] at bound
  exact bound

/-- Conditional lower-tail Cantelli inequality. -/
theorem conditionalCantelli_lower_bound {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Coordinate) (threshold : Coordinate)
    (thresholdPositive : 0 < threshold)
    (selectedDeviation : ∀ item, event item = true →
      threshold ≤ distribution.conditionalMean condition value - value item) :
    distribution.conditionalProbability event condition conditionPositive ≤
      distribution.conditionalVariance condition value /
        (distribution.conditionalVariance condition value + threshold ^ 2) := by
  have bound := (distribution.conditioned condition conditionPositive)
    |>.cantelli_lower_bound event value threshold thresholdPositive (by
      intro atom member selected
      rw [distribution.conditioned_expectation_eq_conditionalMean
        condition conditionPositive value]
      exact selectedDeviation atom.item selected)
  rw [distribution.conditioned_probability condition event conditionPositive,
    distribution.conditioned_variance_eq_conditionalVariance
      condition conditionPositive value] at bound
  exact bound

end Distribution

end FiniteMeasure
