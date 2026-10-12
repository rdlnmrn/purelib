module
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
public import Purelib.Measure.Distribution.Conditioning.Moments
import Purelib.Measure.Distribution.Conditioning.Probability
import Purelib.Measure.Distribution.Moments.Basic
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
import Purelib.Measure.Distribution.Moments.Cantelli
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Conditional finite moment inequalities

An explicitly positive conditioning event produces a displayed rational
distribution.  Its expectation, variance, and event probabilities are the
corresponding conditional quantities on the source table.  The ordinary
finite Markov, Chebyshev, and Cantelli inequalities therefore transport
directly, with all hypotheses remaining pointwise and executable.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Variance under the retained positive-event conditioned law equals the original conditional variance. -/
theorem conditioned_variance_eq_conditionalVariance {α : Type}
    (distribution : Measure.Distribution α) (condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Fraction.Rational) :
    (distribution.conditioned condition conditionPositive).variance value =
      distribution.conditionalVariance condition value := by
  unfold variance varianceAround conditionalVariance
  rw [distribution.conditioned_expectation_eq_conditionalMean
      condition conditionPositive value,
    distribution.conditioned_expectation_eq_conditionalMean
      condition conditionPositive]

/-- For a nonnegative observable, a positive lower threshold on an event bounds its conditional probability by
conditional mean divided by threshold. -/
theorem conditionalMarkov_bound {α : Type}
    (distribution : Measure.Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
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

/-- A squared deviation threshold bounds conditional event probability by conditional variance divided by threshold
squared. -/
theorem conditionalChebyshev_bound {α : Type}
    (distribution : Measure.Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
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

/-- An upper deviation threshold bounds conditional probability by conditional variance divided by conditional variance
plus threshold squared. -/
theorem conditionalCantelli_bound {α : Type}
    (distribution : Measure.Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
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

/-- A lower deviation threshold bounds conditional probability by conditional variance divided by conditional variance
plus threshold squared. -/
theorem conditionalCantelli_lower_bound {α : Type}
    (distribution : Measure.Distribution α) (event condition : α → Bool)
    (conditionPositive : 0 < distribution.probability condition)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
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

end

end Distribution

end Purelib.Measure
