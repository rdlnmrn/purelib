module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.EncodedPrefix.Threshold
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine
import Purelib.Measure.Distribution.Sampling.Deviation
public import Purelib.Measure.Distribution.Sampling.Request
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.GaussianInt.Basic

section
@[expose] public section

/-!
# Finite frequency estimation of CCL threshold events

A displayed rational margin makes the threshold decision of every compatible
CCL realization equal to the decision on the original affine input.  The
constructive Bernoulli sample-count request then estimates that exact finite
threshold probability by a finite sample frequency.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested sample count controls omega-threshold frequency error relative to the exact affine event probability.

Every original atom realizes its encoding, whose block budget resolves the supplied positive threshold margin. Tolerance
and failure requests are positive. -/
theorem
  encodedChordalOmegaThresholdFrequency_targetDeviationProbability_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction atom.item).value) ∨
        Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Distribution.requiredEventFrequencySampleCount
          tolerance failure)).probability
      (Distribution.Projective.Chordal.encodedChordalOmegaThresholdFrequencyTargetDeviation distribution
        fraction
        (Distribution.requiredEventFrequencySampleCount
          tolerance failure)
        points threshold tolerance) < failure := by
  let realizedEvent : index → Bool :=
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (points item)
  let exactEvent : index → Bool :=
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)
  let count :=
    Distribution.requiredEventFrequencySampleCount
      tolerance failure
  have probabilityEqual : distribution.probability realizedEvent =
      distribution.probability exactEvent :=
    CCL.EncodedPrefix.encodedChordalOmegaProbe_thresholdProbability_eq_values_of_margin
      distribution fraction numeratorNonzero threshold margin marginPositive
      separated enough points pointsRealize
  calc
    (distribution.iidSamples count).probability
          (Distribution.Projective.Chordal.encodedChordalOmegaThresholdFrequencyTargetDeviation distribution
            fraction count points threshold tolerance) =
        (distribution.iidSamples count).probability
          (Distribution.eventFrequencyDeviation
            distribution count realizedEvent tolerance) := by
      apply (distribution.iidSamples count).probability_congr
      intro sample
      unfold Distribution.Projective.Chordal.encodedChordalOmegaThresholdFrequencyTargetDeviation
      unfold Distribution.eventFrequencyDeviation
      unfold Distribution.sampleMeanDeviation
      change decide (tolerance ^ 2 ≤
          (Distribution.sampleMean count
              (Distribution.indicator realizedEvent)
              sample - distribution.probability exactEvent) ^ 2) =
        decide (tolerance ^ 2 ≤
          (Distribution.sampleMean count
              (Distribution.indicator realizedEvent)
              sample - distribution.expectation
                (Distribution.indicator realizedEvent)) ^ 2)
      rw [distribution.expectation_indicator, probabilityEqual]
    _ < failure :=
      distribution.iidSamples_eventFrequency_deviationProbability_lt_requested
        realizedEvent tolerance tolerancePositive failure failurePositive

end Purelib.Measure.CCL.EncodedPrefix

end
