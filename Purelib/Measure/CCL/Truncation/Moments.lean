module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.BinaryPrefix.Averaging
import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.BinaryPrefix.Distribution.Consistency
import Purelib.Measure.BinaryPrefix.Distribution.Variance
import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.RawParser.Truncation
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.CCL.Truncation.Basic
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite-depth laws of CCL truncation points

The symbolic fair-bit distribution on a displayed raw extension frontier can
be pushed through the parser's explicit projective truncation.  The result is
an ordinary finite distribution of constructive projective points.  No claim
is made about a limiting decoder value or a geometric pushforward measure.
-/

namespace Purelib.Measure.CCL.Truncation

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Backward averaging the parsed-word probe gives its expectation under the deeper truncation law. -/
theorem rawTruncationDistribution_expectation_backward
    (stem : List.BinaryPrefix.CCLMeasureWord) (depth extra : Nat)
    (probe : Line.GaussianLine → Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem depth).expectation
        (BinaryPrefix.rawBackwardMean extra (fun word => probe (RawParser.rawTruncation word))) =
      (CCL.Truncation.rawTruncationDistribution stem (depth + extra)).expectation probe := by
  rw [CCL.Truncation.rawTruncationDistribution_expectation]
  exact BinaryPrefix.rawExtensionDistribution_expectation_backward stem depth
    (fun word => probe (RawParser.rawTruncation word)) extra

/-- Deeper truncation variance splits into expected backward variance and variance of the backward mean.

Both terms use the original binary-extension law at the retained stem and base depth, with the same additional averaging
depth and parsed-word probe. -/
theorem rawTruncationDistribution_totalVariance_backward
    (stem : List.BinaryPrefix.CCLMeasureWord) (depth extra : Nat)
    (probe : Line.GaussianLine → Fraction.Rational) :
    (CCL.Truncation.rawTruncationDistribution stem (depth + extra)).variance probe =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
          (BinaryPrefix.rawBackwardVariance extra
            (fun word => probe (RawParser.rawTruncation word))) +
        (BinaryPrefix.rawExtensionDistribution stem depth).variance
          (BinaryPrefix.rawBackwardMean extra
            (fun word => probe (RawParser.rawTruncation word))) := by
  have mapVariance :
      (CCL.Truncation.rawTruncationDistribution stem (depth + extra)).variance probe =
        (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).variance
          (fun word => probe (RawParser.rawTruncation word)) := by
    rw [CCL.Truncation.rawTruncationDistribution]
    rw [(Distribution.map _ _).variance_eq_secondMoment_sub_sq,
      (BinaryPrefix.rawExtensionDistribution stem
        (depth + extra)).variance_eq_secondMoment_sub_sq,
      (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).map_expectation,
      (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).map_expectation]
  rw [mapVariance]
  exact BinaryPrefix.rawExtensionDistribution_totalVariance_backward stem depth
    (fun word => probe (RawParser.rawTruncation word)) extra

end Purelib.Measure.CCL.Truncation

end
