module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Encoder.Blocks
public import Purelib.Approximation.Rational.Budget.ReciprocalSquare
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.CCL.Cylinder.Sampling
public import Purelib.Measure.CCL.EncodedPrefix.Concentration
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Distribution.Sampling.Deviation
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Finite iid sampling certificates from CCL encoder cylinders

A squared-sensitive probe on one finite CCL cylinder has an explicit rational
variance budget.  Substituting that budget into the constructive Chebyshev
sample-count request yields a finite iid sample-mean deviation certificate.
For an actual encoder run, every quantity in the request is executable.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The encoded cylinder's variance budget supplies a sample count meeting the requested deviation probability.

Every retained point realizes the same fraction encoding. The squared-sensitive probe has nonnegative factor, and the
tolerance and failure request are positive. -/
theorem
  encodedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    {index : Type}
    (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0)
    (distribution : Measure.Distribution index)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
        (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Distribution.requiredChebyshevSampleCount
          (CCL.EncodedPrefix.encodedProbeVarianceBudget fraction numeratorNonzero factor)
          threshold failure)).probability
      (distribution.sampleMeanDeviation
        (Distribution.requiredChebyshevSampleCount
          (CCL.EncodedPrefix.encodedProbeVarianceBudget fraction numeratorNonzero factor)
          threshold failure)
        (fun item => probe (points item)) threshold) < failure := by
  exact CCL.Cylinder.projectiveRealizedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    distribution (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).point
    (Encoder.Blocks.encodeBlocks_realizes fraction numeratorNonzero)
    points pointsRealize probe factor factorNonnegative sensitive
    threshold thresholdPositive failure failurePositive

/-- The encoded omega-probe variance budget supplies a sample count whose deviation probability is below the positive
failure request. -/
theorem
  encodedChordalOmegaProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    {index : Type}
    (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0)
    (distribution : Measure.Distribution index)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
        (points atom.item))
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Distribution.requiredChebyshevSampleCount
          (CCL.EncodedPrefix.encodedProbeVarianceBudget fraction numeratorNonzero 2)
          threshold failure)).probability
      (distribution.sampleMeanDeviation
        (Distribution.requiredChebyshevSampleCount
          (CCL.EncodedPrefix.encodedProbeVarianceBudget fraction numeratorNonzero 2)
          threshold failure)
        (fun item => Chordal.Probe.chordalOmegaProbe (points item)) threshold) < failure :=
  CCL.EncodedPrefix.encodedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    fraction numeratorNonzero distribution points pointsRealize
    Chordal.Probe.chordalOmegaProbe 2 (by decide) Chordal.Probe.chordalOmegaProbe_squaredSensitive
    threshold thresholdPositive failure failurePositive

end Purelib.Measure.CCL.EncodedPrefix

end
