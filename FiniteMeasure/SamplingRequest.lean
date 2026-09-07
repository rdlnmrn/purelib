import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments
import FiniteMeasure.Sampling

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

namespace FiniteMeasure

namespace Distribution

/-- A positive finite sample count sufficient for a Chebyshev failure request
under a displayed rational variance upper bound. -/
def requiredChebyshevSampleCount
    (varianceBudget threshold failure : Coordinate) : Nat :=
  Nat.succ (RFAP.ConstructiveFraction.ceilNat
    (varianceBudget / (failure * threshold ^ 2)))

theorem requiredChebyshevSampleCount_positive
    (varianceBudget threshold failure : Coordinate) :
    0 < ((requiredChebyshevSampleCount
      varianceBudget threshold failure : Nat) : Coordinate) := by
  apply RFAP.ConstructiveFraction.natCast_pos_direct
  unfold requiredChebyshevSampleCount
  exact Nat.zero_lt_succ _

private theorem requiredChebyshev_ratio_lt_count
    (varianceBudget threshold failure : Coordinate)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (thresholdPositive : 0 < threshold)
    (failurePositive : 0 < failure) :
    varianceBudget / (failure * threshold ^ 2) <
      ((requiredChebyshevSampleCount
        varianceBudget threshold failure : Nat) : Coordinate) := by
  have squarePositive : 0 < threshold ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2
  have denominatorPositive : 0 < failure * threshold ^ 2 :=
    RFAP.ConstructiveFraction.mul_pos_direct failurePositive squarePositive
  let ratio := varianceBudget / (failure * threshold ^ 2)
  have ratioNonnegative : 0 ≤ ratio :=
    RFAP.ConstructiveFraction.div_nonneg_direct varianceBudgetNonnegative
      denominatorPositive.le
  have ratioLeCeiling : ratio ≤
      (RFAP.ConstructiveFraction.ceilNat ratio : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtSuccessor :
      (RFAP.ConstructiveFraction.ceilNat ratio : Coordinate) <
        (Nat.succ (RFAP.ConstructiveFraction.ceilNat ratio) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct (Nat.lt_succ_self _)
  exact ratioLeCeiling.trans_lt ceilingLtSuccessor

/-- The computed finite sample count makes the rational Chebyshev expression
strictly smaller than the requested positive failure budget. -/
theorem requiredChebyshevSampleCount_accurate
    (varianceBudget threshold failure : Coordinate)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (thresholdPositive : 0 < threshold)
    (failurePositive : 0 < failure) :
    (varianceBudget /
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Coordinate)) /
      threshold ^ 2 < failure := by
  have squarePositive : 0 < threshold ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2
  have failureTimesSquarePositive : 0 < failure * threshold ^ 2 :=
    RFAP.ConstructiveFraction.mul_pos_direct failurePositive squarePositive
  have countPositive := requiredChebyshevSampleCount_positive
    varianceBudget threshold failure
  have ratioSmall := requiredChebyshev_ratio_lt_count
    varianceBudget threshold failure varianceBudgetNonnegative
    thresholdPositive failurePositive
  have numeratorSmall : varianceBudget <
      (failure * threshold ^ 2) *
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Coordinate) := by
    have crossed := (RFAP.ConstructiveFraction.div_lt_iff_pos
      failureTimesSquarePositive).1 ratioSmall
    calc
      varianceBudget <
          (requiredChebyshevSampleCount
            varianceBudget threshold failure : Coordinate) *
            (failure * threshold ^ 2) := crossed
      _ = (failure * threshold ^ 2) *
          (requiredChebyshevSampleCount
            varianceBudget threshold failure : Coordinate) := by ring1
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos squarePositive).2
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos countPositive).2
  exact numeratorSmall

private theorem div_div_le_div_div_of_le
    {left right firstDenominator secondDenominator : Coordinate}
    (order : left ≤ right)
    (firstPositive : 0 < firstDenominator)
    (secondPositive : 0 < secondDenominator) :
    (left / firstDenominator) / secondDenominator ≤
      (right / firstDenominator) / secondDenominator := by
  change (left * firstDenominator⁻¹) * secondDenominator⁻¹ ≤
    (right * firstDenominator⁻¹) * secondDenominator⁻¹
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct order
      (RFAP.ConstructiveFraction.inv_pos_direct firstPositive).le)
    (RFAP.ConstructiveFraction.inv_pos_direct secondPositive).le

/-- Every larger finite sample count preserves the strict Chebyshev request. -/
theorem requiredChebyshevSampleCount_accurate_of_le
    (varianceBudget threshold failure : Coordinate)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (thresholdPositive : 0 < threshold)
    (failurePositive : 0 < failure)
    (count : Nat)
    (enough : requiredChebyshevSampleCount
      varianceBudget threshold failure ≤ count) :
    (varianceBudget / (count : Coordinate)) / threshold ^ 2 < failure := by
  have requestedPositive := requiredChebyshevSampleCount_positive
    varianceBudget threshold failure
  have countOrder :
      ((requiredChebyshevSampleCount
        varianceBudget threshold failure : Nat) : Coordinate) ≤
        (count : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct enough
  have squarePositive : 0 < threshold ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2
  have firstDivisionLe : varianceBudget / (count : Coordinate) ≤
      varianceBudget /
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Coordinate) :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      varianceBudgetNonnegative requestedPositive countOrder
  have bothDivisionsLe :
      (varianceBudget / (count : Coordinate)) / threshold ^ 2 ≤
        (varianceBudget /
          (requiredChebyshevSampleCount
            varianceBudget threshold failure : Coordinate)) /
          threshold ^ 2 := by
    change (varianceBudget / (count : Coordinate)) *
        (threshold ^ 2)⁻¹ ≤
      (varianceBudget /
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Coordinate)) *
        (threshold ^ 2)⁻¹
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      firstDivisionLe
      (RFAP.ConstructiveFraction.inv_pos_direct squarePositive).le
  exact bothDivisionsLe.trans_lt
    (requiredChebyshevSampleCount_accurate varianceBudget threshold failure
      varianceBudgetNonnegative thresholdPositive failurePositive)

/-- An explicit variance certificate turns the computed natural sample count
into a strict finite sample-mean deviation-probability certificate. -/
theorem iidSamples_sampleMean_deviationProbability_lt_requested
    {α : Type} (source : Distribution α) (value : α → Coordinate)
    (varianceBudget : Coordinate)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (varianceLe : source.variance value ≤ varianceBudget)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredChebyshevSampleCount varianceBudget threshold failure)).probability
          (source.sampleMeanDeviation
            (requiredChebyshevSampleCount varianceBudget threshold failure)
            value threshold) < failure := by
  let count := requiredChebyshevSampleCount varianceBudget threshold failure
  have countPositive : 0 < (count : Coordinate) :=
    requiredChebyshevSampleCount_positive varianceBudget threshold failure
  have squarePositive : 0 < threshold ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2
  calc
    (source.iidSamples count).probability
          (source.sampleMeanDeviation count value threshold) ≤
        (source.variance value / (count : Coordinate)) / threshold ^ 2 :=
      source.iidSamples_sampleMean_chebyshev value count countPositive
        threshold thresholdPositive
    _ ≤ (varianceBudget / (count : Coordinate)) / threshold ^ 2 :=
      div_div_le_div_div_of_le varianceLe countPositive squarePositive
    _ < failure := requiredChebyshevSampleCount_accurate varianceBudget
      threshold failure varianceBudgetNonnegative thresholdPositive
      failurePositive

/-- Any explicitly supplied sample count above the computed request inherits
the same strict sample-mean deviation guarantee. -/
theorem iidSamples_sampleMean_deviationProbability_lt_of_request_le
    {α : Type} (source : Distribution α) (value : α → Coordinate)
    (varianceBudget : Coordinate)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (varianceLe : source.variance value ≤ varianceBudget)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (count : Nat)
    (enough : requiredChebyshevSampleCount
      varianceBudget threshold failure ≤ count) :
    (source.iidSamples count).probability
      (source.sampleMeanDeviation count value threshold) < failure := by
  have requestedPositive := requiredChebyshevSampleCount_positive
    varianceBudget threshold failure
  have countOrder :
      ((requiredChebyshevSampleCount
        varianceBudget threshold failure : Nat) : Coordinate) ≤
        (count : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct enough
  have countPositive : 0 < (count : Coordinate) :=
    requestedPositive.trans_le countOrder
  have squarePositive : 0 < threshold ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2
  calc
    (source.iidSamples count).probability
          (source.sampleMeanDeviation count value threshold) ≤
        (source.variance value / (count : Coordinate)) / threshold ^ 2 :=
      source.iidSamples_sampleMean_chebyshev value count countPositive
        threshold thresholdPositive
    _ ≤ (varianceBudget / (count : Coordinate)) / threshold ^ 2 :=
      div_div_le_div_div_of_le varianceLe countPositive squarePositive
    _ < failure := requiredChebyshevSampleCount_accurate_of_le varianceBudget
      threshold failure varianceBudgetNonnegative thresholdPositive
      failurePositive count enough

/-! ## Finite event-frequency requests -/

/-- The uniform Bernoulli variance budget gives an executable sample count
for estimating any finite event probability by its sample frequency. -/
def requiredEventFrequencySampleCount
    (threshold failure : Coordinate) : Nat :=
  requiredChebyshevSampleCount (1 / 4) threshold failure

/-- Executable deviation of a finite event frequency from its exact finite
probability. -/
def eventFrequencyDeviation {α : Type} (source : Distribution α)
    (count : Nat) (event : α → Bool) (threshold : Coordinate) :
    List α → Bool :=
  source.sampleMeanDeviation count (indicator event) threshold

/-- The computed finite Bernoulli sample count estimates every executable
event probability within the displayed threshold except on probability
strictly below the requested failure budget. -/
theorem iidSamples_eventFrequency_deviationProbability_lt_requested
    {α : Type} (source : Distribution α) (event : α → Bool)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredEventFrequencySampleCount threshold failure)).probability
      (eventFrequencyDeviation source
        (requiredEventFrequencySampleCount threshold failure)
        event threshold) < failure := by
  exact source.iidSamples_sampleMean_deviationProbability_lt_requested
    (indicator event) (1 / 4) (by decide)
    (source.variance_indicator_le_quarter event)
    threshold thresholdPositive failure failurePositive

/-- Every larger displayed finite sample count preserves the event-frequency
failure guarantee. -/
theorem iidSamples_eventFrequency_deviationProbability_lt_of_request_le
    {α : Type} (source : Distribution α) (event : α → Bool)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (count : Nat)
    (enough : requiredEventFrequencySampleCount threshold failure ≤ count) :
    (source.iidSamples count).probability
      (eventFrequencyDeviation source count event threshold) < failure := by
  exact source.iidSamples_sampleMean_deviationProbability_lt_of_request_le
    (indicator event) (1 / 4) (by decide)
    (source.variance_indicator_le_quarter event)
    threshold thresholdPositive failure failurePositive count enough

end Distribution

end FiniteMeasure
