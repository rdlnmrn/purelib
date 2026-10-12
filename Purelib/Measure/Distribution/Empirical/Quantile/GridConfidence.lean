module
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Rational.Budget.FiniteFamily
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Empirical.Basic
import Purelib.Measure.Distribution.Empirical.Cumulative
public import Purelib.Measure.Distribution.Empirical.Quantile
import Purelib.Measure.Distribution.Quantile.Margin
public import Purelib.Measure.Distribution.Sampling.Cumulative
import Purelib.Measure.Distribution.Sampling.Family
import Purelib.Measure.Event.RationalGrid
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Sampling.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite empirical quantile certificates

Two empirical cumulative frequencies, at explicitly supplied lower and upper
cuts, certify a bracket for an executable empirical lower quantile.  A shared
finite sampling request controls those cuts together with any other displayed
thresholds.  There is no infinite empirical process and no convergence of a
sequence of quantiles.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Grid-frequency accuracy and original endpoint margins bracket the exact nonempty empirical lower quantile. -/
theorem empiricalLowerQuantile_mem_bracket_of_gridWithin
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (tolerance : Fraction.Rational)
    (within : EmpiricalCumulativeGridWithin source thresholds samples.length
      tolerance samples)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    lower < (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ∧
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ≤ upper := by
  apply (empiricalDistribution samples positiveLength)
    |>.lowerQuantile_mem_bracket_of_cumulative_separations_lt source
      level levelPositive levelAtMostOne lower upper tolerance
  · rw [empiricalDistribution_cumulative_eq_eventFrequency]
    exact within lower lowerMember
  · rw [empiricalDistribution_cumulative_eq_eventFrequency]
    exact within upper upperMember
  · exact lowerMargin
  · exact upperMargin

/-- Outside the original grid deviation event, retained cumulative margins bracket the exact empirical lower quantile.
-/
theorem empiricalLowerQuantile_mem_bracket_of_outside_gridDeviation
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (outside : empiricalCumulativeGridDeviation source thresholds
      samples.length tolerance samples = false)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    lower < (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ∧
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ≤ upper := by
  apply source.empiricalLowerQuantile_mem_bracket_of_gridWithin thresholds
    samples positiveLength tolerance
  · exact source.empiricalCumulativeGridWithin_of_outside thresholds
      samples.length tolerance tolerancePositive samples outside
  · exact lowerMember
  · exact upperMember
  · exact lowerMargin
  · exact upperMargin

/-- At positive count and tolerance, quantile bracket escape probability is bounded by the original grid deviation
probability. -/
theorem empiricalLowerQuantileBracketDeviation_probability_le_gridDeviation
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples count).probability
        (empiricalLowerQuantileBracketDeviation count level levelPositive
          levelAtMostOne lower upper) ≤
      (source.iidSamples count).probability
        (empiricalCumulativeGridDeviation source thresholds count
          tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have failure := of_decide_eq_true selected
  rcases failure with ⟨lengthEqual, lowerFailure | upperFailure⟩
  · have samplePositive : 0 < atom.item.length := by
      rw [lengthEqual]
      exact countPositive
    cases deviationSelected :
        empiricalCumulativeGridDeviation source thresholds count tolerance
          atom.item with
    | true => rfl
    | false =>
        have outside : empiricalCumulativeGridDeviation source thresholds
            atom.item.length tolerance atom.item = false := by
          simpa only [lengthEqual] using deviationSelected
        have bracket :=
          source.empiricalLowerQuantile_mem_bracket_of_outside_gridDeviation
            thresholds atom.item samplePositive tolerance tolerancePositive
            outside level levelPositive levelAtMostOne lower upper lowerMember
            upperMember lowerMargin upperMargin
        have quantileEqual := sampleLowerQuantile_eq_of_positive atom.item
          samplePositive level levelPositive levelAtMostOne
        rw [quantileEqual] at lowerFailure
        exact (not_le_of_gt bracket.1 lowerFailure).elim
  · have samplePositive : 0 < atom.item.length := by
      rw [lengthEqual]
      exact countPositive
    cases deviationSelected :
        empiricalCumulativeGridDeviation source thresholds count tolerance
          atom.item with
    | true => rfl
    | false =>
        have outside : empiricalCumulativeGridDeviation source thresholds
            atom.item.length tolerance atom.item = false := by
          simpa only [lengthEqual] using deviationSelected
        have bracket :=
          source.empiricalLowerQuantile_mem_bracket_of_outside_gridDeviation
            thresholds atom.item samplePositive tolerance tolerancePositive
            outside level levelPositive levelAtMostOne lower upper lowerMember
            upperMember lowerMargin upperMargin
        have quantileEqual := sampleLowerQuantile_eq_of_positive atom.item
          samplePositive level levelPositive levelAtMostOne
        rw [quantileEqual] at upperFailure
        exact (not_lt_of_ge bracket.2 upperFailure).elim

/-- The exact grid sample request makes quantile bracket escape probability smaller than the positive failure tolerance.

Both endpoints belong to the retained grid and satisfy the original strict lower and weak upper cumulative margins. -/
theorem iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalLowerQuantileBracketDeviation
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  let count := requiredCumulativeGridSampleCount thresholds tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source.empiricalLowerQuantileBracketDeviation_probability_le_gridDeviation
    thresholds count countPositive tolerance tolerancePositive level
    levelPositive levelAtMostOne lower upper lowerMember upperMember
    lowerMargin upperMargin).trans_lt
      (source.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
        thresholds tolerance tolerancePositive failure failurePositive)

/-- The exact grid sample request controls median bracket escape using the original level-one-half endpoint margins. -/
theorem iidSamples_empiricalMedianBracketDeviation_lt_requested
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (lower upper : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < 1 / 2)
    (upperMargin : 1 / 2 + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalMedianBracketDeviation
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        lower upper) < failure := by
  exact source.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
    thresholds tolerance tolerancePositive failure failurePositive
    (1 / 2) (by decide) (by decide) lower upper lowerMember upperMember
    lowerMargin upperMargin

end Distribution

end Purelib.Measure

end
