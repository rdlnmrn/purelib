module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Moments.Correlation
import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Measure.Distribution.Moments.Lp
import Purelib.Measure.Distribution.Pure.EssentialMaximum
import Purelib.Measure.Distribution.Pure.Lp
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.Deviation
import Purelib.Measure.Distribution.Sampling.Moments
import Purelib.Measure.Distribution.Sampling.Request
import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Distribution.TotalVariation.Support
import Purelib.Measure.Jensen
import Purelib.Measure.Sampling.Statistic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Coin.Law

import Purelib.Tactic.QuotientFreeOmega
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
import Purelib.Measure.Distribution.Kolmogorov.TotalVariation
import Purelib.Measure.Distribution.Quantile.Kolmogorov
import Purelib.Measure.Distribution.Mixture.EssentialMaximum
import Purelib.Measure.Distribution.Mixture.Lp
import Purelib.Measure.EventAlgebra.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Mixture.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber coinPayoff fairCoin reverseCoinNumber)
open Purelib.Examples.Measure.Distribution.Coin.Law (coinNumberLaw)

/-- The rational mixture coefficient three quarters, with complementary weight one quarter. -/
def mostlyFalseWeight : MixingWeight where
  coefficient := 3 / 4
  nonnegative := by decide
  atMostOne := by decide

/-- The quarter-heads coin formed from the original false and true singleton atom tables. -/
def quarterCoin : Distribution Bool :=
  (Distribution.pure false).mixture (Distribution.pure true)
    mostlyFalseWeight

/-- The numeric pushforward of the quarter-heads coin. -/
def quarterCoinNumberLaw : Distribution
  Fraction.Rational :=
  quarterCoin.map coinNumber

/-- The coin assigning mass three fifths to tails and two fifths to heads. -/
def twoFifthsHeadsCoin : Distribution Bool
  where
  atoms :=
    [⟨false, 3 / 5, by decide⟩,
      ⟨true, 2 / 5, by decide⟩]
  total_one := by decide

/-- The numeric pushforward of the two-fifths-heads coin. -/
def twoFifthsHeadsNumberLaw : Distribution
  Fraction.Rational :=
  twoFifthsHeadsCoin.map coinNumber

/-- The tails mixture coefficient is strictly positive. -/
theorem mostlyFalseWeight_coefficient_positive
  :
    0 < mostlyFalseWeight.coefficient := by
  decide

/-- The heads mixture coefficient is strictly positive. -/
theorem mostlyFalseWeight_complement_positive :
    0 < mostlyFalseWeight.complement := by
  decide

/-- The point mass at heads has powered L3 coin-number value one. -/
example : (Distribution.pure true).poweredLp 3 coinNumber = 1 := by
  rw [Distribution.pure_poweredLp]
  decide

/-- The point mass at tails has essential maximum coin-number magnitude zero. -/
example : (Distribution.pure false).essentialMaximumMagnitude coinNumber =
    0 := by
  rw [Distribution.pure_essentialMaximumMagnitude]
  decide

/-- The retained quarter-heads atom table has length two. -/
example : quarterCoin.atoms.length = 2 := by
  decide

/-- The quarter-heads coin assigns heads probability one quarter. -/
example : quarterCoin.probability (fun outcome => outcome) = 1 / 4 :=
  by
  decide

/-- The fair and quarter-heads numeric laws have Kolmogorov distance one quarter. -/
theorem
  coinNumberLawKolmogorovDistance_quarterCoinNumberLaw
  :
    coinNumberLaw.kolmogorovDistance
      quarterCoinNumberLaw =
    1 / 4 := by
  decide

/-- The compared numeric coin laws have a two-point comparison support. -/
example : coinNumberLaw.comparisonSupportCardinality
  quarterCoinNumberLaw =
    2 := by
  decide

/-- The two-point support bounds total variation by one half through Kolmogorov distance. -/
example : coinNumberLaw.totalVariationDistance
  quarterCoinNumberLaw ≤
    1 / 2 := by
  have bound :=
    coinNumberLaw
      |>.totalVariationDistance_le_supportCardinality_mulKolmogorovDistance
        quarterCoinNumberLaw
  rw [show coinNumberLaw.comparisonSupportCardinality
      quarterCoinNumberLaw = 2 by decide,
    coinNumberLawKolmogorovDistance_quarterCoinNumberLaw] at bound
  calc
    coinNumberLaw.totalVariationDistance
      quarterCoinNumberLaw ≤
        (2 : Fraction.Rational) * (1 / 4) := bound
    _ = 1 / 2 := by decide

/-- Every cumulative probability differs by at most one quarter between the fair and quarter-heads laws. -/
example (cut : Fraction.Rational) :
    Distance.rationalSeparation (coinNumberLaw.cumulative cut)
        (quarterCoinNumberLaw.cumulative cut) ≤ 1 / 4 := by
  have global : coinNumberLaw.kolmogorovDistance
      quarterCoinNumberLaw ≤ 1 / 4 :=
    coinNumberLawKolmogorovDistance_quarterCoinNumberLaw.le
  exact (coinNumberLaw.cumulative_separation_leKolmogorovDistance
    quarterCoinNumberLaw cut).trans global

/-- The two-fifths-heads numeric law has Kolmogorov distance one tenth from the fair law. -/
example : twoFifthsHeadsNumberLaw.kolmogorovDistance
  coinNumberLaw =
    1 / 10 := by
  decide

/-- The lower three-quarter quantile of the perturbed coin lies strictly above zero and at most one. -/
example :
    0 < twoFifthsHeadsNumberLaw.lowerQuantile
          (3 / 4) (by decide) (by decide) ∧
      twoFifthsHeadsNumberLaw.lowerQuantile
          (3 / 4) (by decide) (by decide) ≤ 1 :=
  twoFifthsHeadsNumberLaw
    |>.lowerQuantile_mem_bracket_ofKolmogorovDistance_lt
      coinNumberLaw (3 / 4) (by decide) (by decide) 0 1 (1 / 8)
        (by decide) (by decide) (by decide)

/-- The quarter-heads coin-number expectation is one quarter. -/
example : quarterCoin.expectation
  coinNumber = 1 / 4 := by
  decide

/-- The essential maximum of a positive coin mixture is the maximum of its two component maxima. -/
example : quarterCoin.essentialMaximumMagnitude
  coinNumber =
    max ((Distribution.pure false).essentialMaximumMagnitude coinNumber)
      ((Distribution.pure true).essentialMaximumMagnitude coinNumber) := by
  unfold quarterCoin
  exact (Distribution.pure false).mixture_essentialMaximumMagnitude_eq_max
    (Distribution.pure true) mostlyFalseWeight
    mostlyFalseWeight_coefficient_positive
    mostlyFalseWeight_complement_positive
      coinNumber

/-- The quarter-heads coin-number essential maximum is one. -/
example : quarterCoin.essentialMaximumMagnitude
  coinNumber = 1 := by
  decide

/-- The mixture's powered L3 value is the weighted sum of the component values. -/
example : quarterCoin.poweredLp 3
  coinNumber =
    mostlyFalseWeight.coefficient *
        (Distribution.pure false).poweredLp 3 coinNumber +
      mostlyFalseWeight.complement *
        (Distribution.pure true).poweredLp 3 coinNumber := by
  unfold quarterCoin
  exact (Distribution.pure false).mixture_poweredLp
    (Distribution.pure true) mostlyFalseWeight 3
      coinNumber

/-- The quarter-heads coin-number powered L3 value is one quarter. -/
example : quarterCoin.poweredLp 3
  coinNumber = 1 / 4 := by
  decide

/-- The mixture's L1 distance is the weighted sum of the component distances. -/
example : quarterCoin.l1Distance
  coinNumber reverseCoinNumber =
    mostlyFalseWeight.coefficient *
        (Distribution.pure false).l1Distance coinNumber
          reverseCoinNumber +
      mostlyFalseWeight.complement *
        (Distribution.pure true).l1Distance
          coinNumber reverseCoinNumber := by
  unfold quarterCoin
  exact (Distribution.pure false).mixture_l1Distance
    (Distribution.pure true) mostlyFalseWeight
      coinNumber reverseCoinNumber

/-- The quarter-heads coin-number variance is three sixteenths. -/
example : quarterCoin.variance
  coinNumber = 3 / 16 := by
  decide

/-- The fair-coin variance is the squared L2 distance from its expectation. -/
example : fairCoin.variance coinNumber =
    fairCoin.poweredL2Distance coinNumber
      (fun _ => fairCoin.expectation coinNumber) :=
  fairCoin.variance_eq_poweredL2Distance_expectation
    coinNumber

/-- The fair-coin variance is bounded by its second moment. -/
example : fairCoin.variance coinNumber ≤
  fairCoin.poweredL2 coinNumber :=
  fairCoin.variance_le_poweredL2 coinNumber

/-- Zero coin variance is equivalent to almost-everywhere equality with its expectation. -/
example : fairCoin.variance coinNumber = 0 ↔
    fairCoin.EqualAlmostEverywhere coinNumber
      (fun _ => fairCoin.expectation coinNumber) :=
  fairCoin.variance_eq_zero_iff_equalAlmostEverywhere_expectation
    coinNumber

/-- Variance about any rational center splits into the variance and squared mean displacement. -/
example (center : Fraction.Rational) :
    fairCoin.varianceAround coinNumber center =
      fairCoin.variance coinNumber +
        (fairCoin.expectation coinNumber - center) ^ 2
          :=
  fairCoin.varianceAround_eq_variance_add_mean_sub_sq
    coinNumber center

/-- Variance about a center is minimal exactly when that center is the expectation. -/
example (center : Fraction.Rational) :
    fairCoin.varianceAround coinNumber center =
      fairCoin.variance coinNumber ↔
      center = fairCoin.expectation coinNumber :=
  fairCoin.varianceAround_eq_variance_iff_center_eq_expectation
    coinNumber center

/-- The coin mixture variance splits into the weighted component variances and between-mean correction. -/
example : quarterCoin.variance
  coinNumber =
    mostlyFalseWeight.coefficient *
        (Distribution.pure false).variance coinNumber +
      mostlyFalseWeight.complement *
        (Distribution.pure true).variance coinNumber +
      mostlyFalseWeight.coefficient *
        mostlyFalseWeight.complement *
        ((Distribution.pure false).expectation coinNumber -
          (Distribution.pure true).expectation coinNumber) ^ 2 :=
  (Distribution.pure false).mixture_variance
    (Distribution.pure true) mostlyFalseWeight
      coinNumber

/-- The squared coin covariance is bounded by the product of the two variances. -/
example : fairCoin.covariance coinNumber
  reverseCoinNumber ^ 2 ≤
    fairCoin.variance coinNumber *
      fairCoin.variance reverseCoinNumber :=
  fairCoin.covariance_sq_le_variance_mul coinNumber
    reverseCoinNumber

/-- The squared correlation of the two coin indicators lies in the unit interval. -/
example : 0 ≤ fairCoin.squaredCorrelation coinNumber
  reverseCoinNumber ∧
    fairCoin.squaredCorrelation coinNumber
      reverseCoinNumber ≤ 1 :=
  fairCoin.squaredCorrelation_mem_unit coinNumber
    reverseCoinNumber (by decide)

/-- The two complementary coin indicators have squared correlation one. -/
example : fairCoin.squaredCorrelation coinNumber
  reverseCoinNumber = 1 := by
  decide

/-- Adding seven to one coin indicator preserves its covariance with the other. -/
example : fairCoin.covariance
      (fun outcome => coinNumber outcome + 7)
        reverseCoinNumber =
    fairCoin.covariance coinNumber
      reverseCoinNumber :=
  fairCoin.covariance_add_constant_left coinNumber
    reverseCoinNumber 7

/-- The sum and difference of the coin indicators satisfy the variance parallelogram identity. -/
example : fairCoin.variance
      (fun outcome => coinNumber outcome +
        reverseCoinNumber outcome) +
        fairCoin.variance
          (fun outcome => coinNumber outcome -
            reverseCoinNumber outcome) =
    2 * fairCoin.variance coinNumber +
      2 * fairCoin.variance reverseCoinNumber :=
  fairCoin.variance_parallelogram coinNumber
    reverseCoinNumber

/-- Twice the coin covariance is bounded by the sum of the variances. -/
example : 2 * fairCoin.covariance coinNumber
  reverseCoinNumber ≤
    fairCoin.variance coinNumber +
      fairCoin.variance reverseCoinNumber :=
  fairCoin.two_mul_covariance_le_variance_add
    coinNumber reverseCoinNumber

/-- The fair coin-number expectation satisfies the square Jensen inequality. -/
example : fairCoin.expectation coinNumber ^ 2 ≤
    fairCoin.expectation (fun outcome => coinNumber
      outcome ^ 2) :=
  fairCoin.jensen_square coinNumber

/-- The absolute mean coin payoff is bounded by the mean absolute payoff. -/
example : Distance.rationalSeparation (fairCoin.expectation
  coinPayoff) 0 ≤
    fairCoin.expectation (fun outcome =>
      Distance.rationalSeparation (coinPayoff outcome) 0) :=
  fairCoin.jensen_rationalSeparation_zero coinPayoff

/-- The complementary coin indicators attain equality in the covariance-square bound. -/
example : fairCoin.covariance coinNumber
  reverseCoinNumber ^ 2 =
    fairCoin.variance coinNumber *
      fairCoin.variance reverseCoinNumber := by
  decide

/-- Four retained independent fair tosses have sixteen atoms. -/
example : (fairCoin.iidSamples 4).atoms.length = 16 := by
  decide

/-- The retained independent coin sample table has the original atom-count power as its length. -/
example (count : Nat) :
    (fairCoin.iidSamples count).atoms.length =
      fairCoin.atoms.length ^ count :=
  fairCoin.iidSamples_atoms_length count

/-- Every retained independent sample has its requested length with probability one. -/
example (count : Nat) :
    (fairCoin.iidSamples count).probability
      (fun sample => decide (sample.length = count)) = 1 :=
  fairCoin.iidSamples_probability_sampleLength_eq count

/-- The sum of three independent coin numbers has expectation three halves. -/
example : (fairCoin.iidSamples 3).expectation (Purelib.Measure.sampleSum
  coinNumber) =
    3 / 2 := by
  decide

/-- The mean of four independent coin numbers has variance one sixteenth. -/
example : (fairCoin.iidSamples 4).variance
    (Purelib.Measure.Distribution.sampleMean 4 coinNumber) = 1 / 16 := by
  decide

/-- The four-toss sample mean deviates by at least one half with probability one eighth. -/
example : (fairCoin.iidSamples 4).probability
    (fairCoin.sampleMeanDeviation 4 coinNumber (1 / 2))
      = 1 / 8 := by
  simp only [Distribution.iidSamples_succ, Distribution.map_probability,
    Distribution.product_probability_iterated]
  decide

/-- The four-toss sample mean satisfies the original Chebyshev deviation bound. -/
example : (fairCoin.iidSamples 4).probability
      (fairCoin.sampleMeanDeviation 4 coinNumber (1 /
        2)) ≤
    (fairCoin.variance coinNumber / 4) / (1 / 2) ^ 2 :=
  fairCoin.iidSamples_sampleMean_chebyshev coinNumber 4
    (by decide)
    (1 / 2) (by decide)

/-- Tolerance one tenth and failure budget one twentieth request 501 event-frequency samples. -/
example : Purelib.Measure.Distribution.requiredEventFrequencySampleCount
    (1 / 10) (1 / 20) = 501 := by decide

/-- The empirical heads frequency in four tosses has expectation one half. -/
example : (fairCoin.iidSamples 4).expectation
    (Purelib.Measure.Distribution.eventFrequency 4 (fun outcome => outcome)) = 1 / 2 := by
  rw [fairCoin.iidSamples_expectation_eventFrequency
    (fun outcome => outcome) 4 (by decide)]
  rfl

/-- The empirical heads frequency in four tosses has variance one sixteenth. -/
example : (fairCoin.iidSamples 4).variance
    (Purelib.Measure.Distribution.eventFrequency 4 (fun outcome => outcome)) = 1 / 16 := by
  rw [fairCoin.iidSamples_variance_eventFrequency
    (fun outcome => outcome) 4 (by decide)]
  rfl

end Purelib.Examples.Measure.Distribution.Mixture.Coin.WorkedExamples

end
