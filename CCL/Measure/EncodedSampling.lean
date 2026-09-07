import mathlib.Tactic.QuotientFreeOmega
import CCL.Measure.SquaredCylinderConcentration
import FiniteMeasure.SamplingRequest

/-!
# Finite iid sampling certificates from CCL encoder cylinders

A squared-sensitive probe on one finite CCL cylinder has an explicit rational
variance budget.  Substituting that budget into the constructive Chebyshev
sample-count request yields a finite iid sample-mean deviation certificate.
For an actual encoder run, every quantity in the request is executable.
-/

namespace CCL.FiniteMeasure

/-- The variance allowance emitted by one actual encoder prefix for a probe
with the displayed squared-sensitivity factor. -/
def encodedProbeVarianceBudget
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0)
    (factor : Coordinate) : Coordinate :=
  factor * cylinderSpread
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks

theorem encodedProbeVarianceBudget_nonnegative
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor) :
    0 ≤ encodedProbeVarianceBudget fraction numeratorNonzero factor :=
  RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
    (cylinderSpread_nonneg _)

/-- A finite law supported in one projective CCL cylinder admits an explicit
sample count whose probe sample mean has failure probability below the
requested positive rational budget. -/
theorem projectiveRealizedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
          (factor * cylinderSpread blocks) threshold failure)).probability
      (distribution.sampleMeanDeviation
        (_root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
          (factor * cylinderSpread blocks) threshold failure)
        (fun item => probe (points item)) threshold) < failure := by
  exact distribution.iidSamples_sampleMean_deviationProbability_lt_requested
    (fun item => probe (points item)) (factor * cylinderSpread blocks)
    (RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
      (cylinderSpread_nonneg blocks))
    (projectiveRealizedSquaredProbeVariance_le distribution blocks witness
      witnessRealizes points pointsRealize probe factor factorNonnegative
      sensitive)
    threshold thresholdPositive failure failurePositive

/-- Every actual finite encoder cylinder inherits the constructive
sample-count certificate for an arbitrary squared-sensitive rational probe. -/
theorem encodedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    {index : Type}
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0)
    (distribution : _root_.FiniteMeasure.Distribution index)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
        (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
          (encodedProbeVarianceBudget fraction numeratorNonzero factor)
          threshold failure)).probability
      (distribution.sampleMeanDeviation
        (_root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
          (encodedProbeVarianceBudget fraction numeratorNonzero factor)
          threshold failure)
        (fun item => probe (points item)) threshold) < failure := by
  exact projectiveRealizedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    distribution (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point
    (CCL.Encoder.encodeBlocks_realizes fraction numeratorNonzero)
    points pointsRealize probe factor factorNonnegative sensitive
    threshold thresholdPositive failure failurePositive

/-- Concrete distance-to-`omega` sample-mean certificate for every finite law
supported by an actual encoder cylinder. -/
theorem encodedChordalOmegaProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    {index : Type}
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0)
    (distribution : _root_.FiniteMeasure.Distribution index)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
        (points atom.item))
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
          (encodedProbeVarianceBudget fraction numeratorNonzero 2)
          threshold failure)).probability
      (distribution.sampleMeanDeviation
        (_root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
          (encodedProbeVarianceBudget fraction numeratorNonzero 2)
          threshold failure)
        (fun item => chordalOmegaProbe (points item)) threshold) < failure :=
  encodedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    fraction numeratorNonzero distribution points pointsRealize
    chordalOmegaProbe 2 (by decide) chordalOmegaProbe_squaredSensitive
    threshold thresholdPositive failure failurePositive

end CCL.FiniteMeasure
