module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Approximation.Rational.Budget.FiniteFamily
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Empirical.Basic
public import Purelib.Measure.Distribution.Empirical.KolmogorovConfidence
public import Purelib.Measure.Distribution.Empirical.Quantile
import Purelib.Measure.Distribution.Quantile.Kolmogorov
import Purelib.Measure.Distribution.Sampling.Cumulative
import Purelib.Measure.Distribution.Sampling.Family
import Purelib.Measure.Event.RationalGrid
import Purelib.Measure.Distribution.Kolmogorov.Basic
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
/-- A nonempty empirical law close in Kolmogorov distance has its exact lower quantile within the original
cumulative-margin bracket. -/
theorem empiricalLowerQuantile_mem_bracket_ofKolmogorovDistance_lt
    (source : Distribution Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (tolerance : Fraction.Rational)
    (distanceSmall :
      (empiricalDistribution samples positiveLength).kolmogorovDistance
        source < tolerance)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    lower < (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ∧
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ≤ upper :=
  (empiricalDistribution samples positiveLength)
    |>.lowerQuantile_mem_bracket_ofKolmogorovDistance_lt source
      level levelPositive levelAtMostOne lower upper tolerance distanceSmall
        lowerMargin upperMargin

/-- At positive sample count, original cumulative margins bound quantile bracket escape probability by empirical
Kolmogorov deviation probability. -/
theorem empiricalLowerQuantileBracketDeviation_probability_leKolmogorovDeviation
    (source : Distribution Fraction.Rational)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Fraction.Rational)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples count).probability
        (empiricalLowerQuantileBracketDeviation count level levelPositive
          levelAtMostOne lower upper) ≤
      (source.iidSamples count).probability
        (empiricalKolmogorovDistanceDeviation source count tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have bracketFailure := of_decide_eq_true selected
  rcases bracketFailure with ⟨lengthEqual, escaped⟩
  have samplePositive : 0 < atom.item.length := by
    rw [lengthEqual]
    exact countPositive
  cases distanceSelected : empiricalKolmogorovDistanceDeviation source
      count tolerance atom.item with
  | true => rfl
  | false =>
      have noDistanceFailure : ¬(atom.item.length = count ∧
          tolerance ≤ sampleKolmogorovDistance source atom.item) := by
        unfold empiricalKolmogorovDistanceDeviation at distanceSelected
        exact decide_eq_false_iff_not.mp distanceSelected
      have distanceNotLarge : ¬tolerance ≤
          sampleKolmogorovDistance source atom.item := by
        intro distanceLarge
        exact noDistanceFailure ⟨lengthEqual, distanceLarge⟩
      have sampleDistanceSmall :
          sampleKolmogorovDistance source atom.item < tolerance :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct distanceNotLarge
      have distanceEqual := sampleKolmogorovDistance_eq_of_positive
        source atom.item samplePositive
      rw [distanceEqual] at sampleDistanceSmall
      have bracket :=
        source.empiricalLowerQuantile_mem_bracket_ofKolmogorovDistance_lt
          atom.item samplePositive tolerance sampleDistanceSmall level
          levelPositive levelAtMostOne lower upper lowerMargin upperMargin
      have quantileEqual := sampleLowerQuantile_eq_of_positive atom.item
        samplePositive level levelPositive levelAtMostOne
      rcases escaped with lowerFailure | upperFailure
      · rw [quantileEqual] at lowerFailure
        exact (not_le_of_gt bracket.1 lowerFailure).elim
      · rw [quantileEqual] at upperFailure
        exact (not_lt_of_ge bracket.2 upperFailure).elim

/-- The exact source-grid sample request makes quantile bracket escape probability smaller than the positive failure
tolerance.

The supplied endpoints satisfy margins for the original cumulative law; they need not belong to its support grid. -/
theorem iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested_global
    (source : Distribution Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredKolmogorovSampleCount source tolerance failure)).probability
      (empiricalLowerQuantileBracketDeviation
        (requiredKolmogorovSampleCount source tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  let count := requiredKolmogorovSampleCount source tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredKolmogorovSampleCount
      requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source
    |>.empiricalLowerQuantileBracketDeviation_probability_leKolmogorovDeviation
      count countPositive tolerance level levelPositive levelAtMostOne lower
        upper lowerMargin upperMargin).trans_lt
    (source.iidSamples_empiricalKolmogorovDistanceDeviation_lt_requested
      tolerance tolerancePositive failure failurePositive)

/-- The exact source-grid request controls median bracket escape at original level-one-half cumulative margins. -/
theorem iidSamples_empiricalMedianBracketDeviation_lt_requested_global
    (source : Distribution Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (lower upper : Fraction.Rational)
    (lowerMargin : source.cumulative lower + tolerance < 1 / 2)
    (upperMargin : 1 / 2 + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredKolmogorovSampleCount source tolerance failure)).probability
      (empiricalMedianBracketDeviation
        (requiredKolmogorovSampleCount source tolerance failure)
        lower upper) < failure :=
  source.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested_global
    tolerance tolerancePositive failure failurePositive
      (1 / 2) (by decide) (by decide) lower upper lowerMargin upperMargin
end Distribution

end Purelib.Measure

end
