import CCL.Measure.SquaredPrefixThreshold
import FiniteMeasure.SamplingRequest

/-!
# Finite frequency estimation of CCL threshold events

A displayed rational margin makes the threshold decision of every compatible
CCL realization equal to the decision on the original affine input.  The
constructive Bernoulli sample-count request then estimates that exact finite
threshold probability by a finite sample frequency.
-/

namespace CCL.FiniteMeasure

/-- Deviation of the sampled compatible-realization threshold frequency from
the exact threshold probability of the original affine Gaussian inputs. -/
def encodedChordalOmegaThresholdFrequencyTargetDeviation {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (count : Nat) (points : index → Proj)
    (threshold tolerance : Coordinate) : List index → Bool :=
  fun sample => decide (tolerance ^ 2 ≤
    (_root_.FiniteMeasure.Distribution.sampleMean count
        (_root_.FiniteMeasure.Distribution.indicator
          (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
            chordalOmegaProbe (points item))) sample -
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe
            (CCL.Proj.affine (fraction item).value))) ^ 2)

/-- An actual margin-resolved encoder table admits an explicit finite sample
count whose compatible-realization threshold frequency estimates the exact
affine-input threshold probability with failure probability below the
displayed positive rational request. -/
theorem encodedChordalOmegaThresholdFrequency_targetDeviationProbability_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ chordalOmegaProbe
          (CCL.Proj.affine (fraction atom.item).value) ∨
        chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredEventFrequencySampleCount
          tolerance failure)).probability
      (encodedChordalOmegaThresholdFrequencyTargetDeviation distribution
        fraction
        (_root_.FiniteMeasure.Distribution.requiredEventFrequencySampleCount
          tolerance failure)
        points threshold tolerance) < failure := by
  let realizedEvent : index → Bool :=
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (points item)
  let exactEvent : index → Bool :=
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (CCL.Proj.affine (fraction item).value)
  let count :=
    _root_.FiniteMeasure.Distribution.requiredEventFrequencySampleCount
      tolerance failure
  have probabilityEqual : distribution.probability realizedEvent =
      distribution.probability exactEvent :=
    encodedChordalOmegaProbe_thresholdProbability_eq_values_of_margin
      distribution fraction numeratorNonzero threshold margin marginPositive
      separated enough points pointsRealize
  calc
    (distribution.iidSamples count).probability
          (encodedChordalOmegaThresholdFrequencyTargetDeviation distribution
            fraction count points threshold tolerance) =
        (distribution.iidSamples count).probability
          (_root_.FiniteMeasure.Distribution.eventFrequencyDeviation
            distribution count realizedEvent tolerance) := by
      apply (distribution.iidSamples count).probability_congr
      intro sample
      unfold encodedChordalOmegaThresholdFrequencyTargetDeviation
      unfold _root_.FiniteMeasure.Distribution.eventFrequencyDeviation
      unfold _root_.FiniteMeasure.Distribution.sampleMeanDeviation
      change decide (tolerance ^ 2 ≤
          (_root_.FiniteMeasure.Distribution.sampleMean count
              (_root_.FiniteMeasure.Distribution.indicator realizedEvent)
              sample - distribution.probability exactEvent) ^ 2) =
        decide (tolerance ^ 2 ≤
          (_root_.FiniteMeasure.Distribution.sampleMean count
              (_root_.FiniteMeasure.Distribution.indicator realizedEvent)
              sample - distribution.expectation
                (_root_.FiniteMeasure.Distribution.indicator realizedEvent)) ^ 2)
      rw [distribution.expectation_indicator, probabilityEqual]
    _ < failure :=
      distribution.iidSamples_eventFrequency_deviationProbability_lt_requested
        realizedEvent tolerance tolerancePositive failure failurePositive

end CCL.FiniteMeasure
