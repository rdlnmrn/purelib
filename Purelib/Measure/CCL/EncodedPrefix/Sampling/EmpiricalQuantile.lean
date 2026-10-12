module
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Measure.CCL.EncodedPrefix.Law
public import Purelib.Measure.Distribution.Empirical.GridConfidence
public import Purelib.Measure.Distribution.Empirical.KolmogorovConfidence
public import Purelib.Measure.Distribution.Empirical.Quantile
import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine
import Purelib.Measure.Distribution.Sampling.Cumulative
import Purelib.Measure.Distribution.Empirical.Quantile.GridConfidence
import Purelib.Measure.Distribution.Empirical.Quantile.KolmogorovConfidence
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Empirical quantiles of actual CCL encoder probes

The encoder's computed homogeneous point and its reconstructed affine input
have exactly the same chordal distance-to-`omega` value.  Consequently their
finite pushforward tables are equal, and the constructive empirical-quantile
request applies directly to samples of the encoded observable.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

section
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Measure
/-- Samples of the encoded omega-probe law meet the requested empirical cumulative-grid confidence bound.

The comparison law is the exact affine-value law, with the original finite threshold list and positive tolerance and
failure request. -/
theorem
  encodedChordalOmegaProbe_iidSamples_empiricalCumulativeGridDistance_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    ((CCL.EncodedPrefix.encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (Distribution.empiricalCumulativeGridDistanceDeviation
        (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction) thresholds
        (Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)
        tolerance) < failure := by
  rw [CCL.EncodedPrefix.encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalCumulativeGridDistanceDeviation_lt_requested
      thresholds tolerance tolerancePositive failure failurePositive

/-- The requested encoded omega-probe sample count bounds empirical Kolmogorov error against the affine-value law. -/
theorem
  encodedChordalOmegaProbe_iidSamples_empiricalKolmogorovDistance_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    ((CCL.EncodedPrefix.encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (Distribution.requiredKolmogorovSampleCount
          (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)).probability
      (Distribution.empiricalKolmogorovDistanceDeviation
        (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
        (Distribution.requiredKolmogorovSampleCount
          (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)
          tolerance) < failure := by
  rw [CCL.EncodedPrefix.encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalKolmogorovDistanceDeviation_lt_requested
      tolerance tolerancePositive failure failurePositive

/-- Grid-based sampling brackets the encoded omega-probe empirical quantile with the requested confidence.

Both bracket endpoints belong to the retained threshold grid, and the exact affine cumulative law satisfies the supplied
lower and upper margins at the valid quantile level. -/
theorem
  encodedChordalOmegaProbe_iidSamples_empiricalQuantileBracket_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin :
      (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction).cumulative lower +
        tolerance < level)
    (upperMargin : level + tolerance ≤
      (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction).cumulative upper) :
    ((CCL.EncodedPrefix.encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (Distribution.empiricalLowerQuantileBracketDeviation
        (Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  rw [CCL.EncodedPrefix.encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
      thresholds tolerance tolerancePositive failure failurePositive level
      levelPositive levelAtMostOne lower upper lowerMember upperMember
      lowerMargin upperMargin

/-- Global cumulative confidence brackets the encoded omega-probe empirical quantile with the requested probability.

The exact affine law supplies the endpoint margins at a level in `(0, 1]`; the sample count uses that same law's finite
Kolmogorov bound. -/
theorem
  encodedChordalOmegaProbe_iidSamples_empiricalQuantileBracket_lt_requested_global
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMargin :
      (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction).cumulative lower +
        tolerance < level)
    (upperMargin : level + tolerance ≤
      (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction).cumulative upper) :
    ((CCL.EncodedPrefix.encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (Distribution.requiredKolmogorovSampleCount
          (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)).probability
      (Distribution.empiricalLowerQuantileBracketDeviation
        (Distribution.requiredKolmogorovSampleCount
          (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  rw [CCL.EncodedPrefix.encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested_global
      tolerance tolerancePositive failure failurePositive level levelPositive
        levelAtMostOne lower upper lowerMargin upperMargin

end

end Purelib.Measure.CCL.EncodedPrefix

end
