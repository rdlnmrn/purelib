module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Sampling.Family
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Simultaneous finite CCL threshold-frequency estimation

One finite iid sample of a compatible realization table can estimate a
displayed list of chordal threshold probabilities simultaneously.  A common
positive witness margin identifies each encoded threshold probability with
the exact probability computed from the original affine Gaussian inputs.
The result is a finite survival-function grid certificate; no continuum of
thresholds or infinite sample stream is introduced.
-/

namespace Purelib.Measure.Distribution.Sampling

open Purelib in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Map the exact retained threshold list to at-least events of the original points' chordal omega readings. -/
def encodedChordalOmegaThresholdEvents {index : Type}
    (points : index → Line.GaussianLine) (thresholds : List Fraction.Rational) :
    List (index → Bool) :=
  thresholds.map fun threshold =>
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (points item)

open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Compute a common sample request for the exact chordal omega threshold-event family. -/
def requiredEncodedChordalOmegaThresholdGridSampleCount {index : Type}
    (points : index → Line.GaussianLine) (thresholds : List Fraction.Rational)
    (tolerance failure : Fraction.Rational) : Nat :=
  Distribution.requiredEventFamilyFrequencySampleCount
    (encodedChordalOmegaThresholdEvents points thresholds) tolerance failure

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Select samples with a frequency deviation in the exact retained chordal omega threshold-event family. -/
def encodedChordalOmegaThresholdGridDeviation {index : Type}
    (distribution : Measure.Distribution index)
    (points : index → Line.GaussianLine) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational) : List index → Bool :=
  Distribution.simultaneousEventFrequencyDeviation
    distribution (encodedChordalOmegaThresholdEvents points thresholds)
      count tolerance

/-- The exact family sample request makes simultaneous chordal omega threshold-frequency deviation probability smaller
than the positive failure tolerance. -/
theorem encodedChordalOmegaThresholdGrid_deviationProbability_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (points : index → Line.GaussianLine) (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
      (requiredEncodedChordalOmegaThresholdGridSampleCount points thresholds
        tolerance failure)).probability
      (encodedChordalOmegaThresholdGridDeviation distribution points
        thresholds
        (requiredEncodedChordalOmegaThresholdGridSampleCount points thresholds
          tolerance failure)
        tolerance) < failure :=
  distribution
    |>.iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
      (encodedChordalOmegaThresholdEvents points thresholds)
      tolerance tolerancePositive failure failurePositive
end Purelib.Measure.Distribution.Sampling

end
