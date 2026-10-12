module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Square
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Enclosure
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Variance
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.CCL.Encoding (Block)
open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Variance enclosures from finite CCL prefixes

Separate CCL sensitivity certificates for a rational probe and its square
give finite enclosures of the mean and second moment.  Exact constructive
interval squaring and subtraction then enclose the finite variance.  Adding
displayed CCL suffixes narrows the complete variance enclosure.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Enclose variance by subtracting the squared mean enclosure from the second-moment enclosure.

Separate nonnegative sensitivity factors control the probe and its square over the same original certificate
distribution. -/
def prefixFamilyProbeVarianceBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (squareFactor : Fraction.Rational) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.squareProbe probe left) (Function.Rat.squareProbe probe right) ≤
        squareFactor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  (CCL.Prefix.prefixFamilyProbeExpectationBound distribution (Function.Rat.squareProbe probe)
    squareFactor squareFactorNonnegative squareSensitive).sub
  (CCL.Prefix.prefixFamilyProbeExpectationBound distribution probe meanFactor
    meanFactorNonnegative meanSensitive).square

/-- The variance enclosure contains the variance of every probe realization of the retained certificate blocks. -/
theorem prefixFamilyProbeVarianceBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (squareFactor : Fraction.Rational) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.squareProbe probe left) (Function.Rat.squareProbe probe right) ≤
        squareFactor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeVarianceBound distribution probe meanFactor
      meanFactorNonnegative meanSensitive squareFactor
      squareFactorNonnegative squareSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) := by
  have meanInside := CCL.Prefix.prefixFamilyProbeExpectationBound_contains distribution
    probe meanFactor meanFactorNonnegative meanSensitive points pointsRealize
  have secondInside := CCL.Prefix.prefixFamilyProbeExpectationBound_contains distribution
    (Function.Rat.squareProbe probe) squareFactor squareFactorNonnegative squareSensitive
      points pointsRealize
  have meanSquareInside := Interval.square_contains meanInside
  have differenceInside := Interval.sub_contains
    secondInside meanSquareInside
  rw [distribution.variance_eq_secondMoment_sub_sq]
  exact differenceInside

/-- Variance-enclosure width is the second-moment width plus the squared mean-enclosure width. -/
theorem prefixFamilyProbeVarianceBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (squareFactor : Fraction.Rational) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.squareProbe probe left) (Function.Rat.squareProbe probe right) ≤
        squareFactor * Chordal.Basic.chordalSq left right) :
    (prefixFamilyProbeVarianceBound distribution probe meanFactor
      meanFactorNonnegative meanSensitive squareFactor
      squareFactorNonnegative squareSensitive).width =
      (CCL.Prefix.prefixFamilyProbeExpectationBound distribution (Function.Rat.squareProbe probe)
        squareFactor squareFactorNonnegative squareSensitive).width +
      (CCL.Prefix.prefixFamilyProbeExpectationBound distribution probe meanFactor
        meanFactorNonnegative meanSensitive).square.width := by
  unfold prefixFamilyProbeVarianceBound
  exact Interval.sub_width _ _

/-- Construct the second-moment-minus-squared-mean enclosure after retained suffix extensions.

The original certificate distribution, probe and witnesses are fixed, with realization evidence for every extended
prefix. -/
def extendedPrefixFamilyProbeVarianceBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (squareFactor : Fraction.Rational) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.squareProbe probe left) (Function.Rat.squareProbe probe right) ≤
        squareFactor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  (CCL.Prefix.extendedPrefixFamilyProbeExpectationBound distribution suffix
    extendedRealizes (Function.Rat.squareProbe probe) squareFactor
      squareFactorNonnegative squareSensitive).sub
  (CCL.Prefix.extendedPrefixFamilyProbeExpectationBound distribution suffix
    extendedRealizes probe meanFactor meanFactorNonnegative
      meanSensitive).square

/-- Extending the certificate blocks refines the variance enclosure built from the same sensitivity data. -/
theorem extendedPrefixFamilyProbeVarianceBound_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (squareFactor : Fraction.Rational) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.squareProbe probe left) (Function.Rat.squareProbe probe right) ≤
        squareFactor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (extendedPrefixFamilyProbeVarianceBound distribution suffix
        extendedRealizes probe meanFactor meanFactorNonnegative meanSensitive
        squareFactor squareFactorNonnegative squareSensitive)
      (prefixFamilyProbeVarianceBound distribution probe meanFactor
        meanFactorNonnegative meanSensitive squareFactor
        squareFactorNonnegative squareSensitive) := by
  apply Interval.Refines.sub
  · exact CCL.Prefix.extendedPrefixFamilyProbeExpectationBound_refines distribution
      suffix extendedRealizes (Function.Rat.squareProbe probe) squareFactor
      squareFactorNonnegative squareSensitive
  · exact (CCL.Prefix.extendedPrefixFamilyProbeExpectationBound_refines distribution
      suffix extendedRealizes probe meanFactor meanFactorNonnegative
      meanSensitive).square

end

end Purelib.Measure.CCL.Prefix

end

section
section
@[expose] public section

/-!
# Covariance enclosures from finite CCL prefixes

Three finite variance enclosures, for two rational probes and their sum,
enclose covariance through the exact rational polarization identity.  This
uses only displayed prefix families, rational interval arithmetic, and
finite weighted sums.
-/

namespace Purelib.Geometry.Projective.Chordal.Probe
namespace ProbeVarianceData

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Use the retained probe-variance data to enclose variance over a completed-prefix certificate law. -/
def prefixFamilyBound {probe :
  Line.GaussianLine → Fraction.Rational}
    (data : Chordal.Probe.ProbeVarianceData probe)
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate) :
    Data.Rat.Interval :=
  CCL.Prefix.prefixFamilyProbeVarianceBound distribution probe
    data.meanFactor data.meanFactorNonnegative data.meanSensitive
    data.squareFactor data.squareFactorNonnegative data.squareSensitive

/-- The variance-data enclosure contains every realizing probe family's variance under the original law. -/
theorem prefixFamilyBound_contains {probe :
  Line.GaussianLine → Fraction.Rational}
    (data : Chordal.Probe.ProbeVarianceData probe)
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (data.prefixFamilyBound distribution).Contains
      (distribution.variance fun certificate => probe (points certificate)) :=
  CCL.Prefix.prefixFamilyProbeVarianceBound_contains distribution probe
    data.meanFactor data.meanFactorNonnegative data.meanSensitive
    data.squareFactor data.squareFactorNonnegative data.squareSensitive
    points pointsRealize

/-- Use the same retained variance data to enclose variance after the supplied prefix extensions. -/
def extendedPrefixFamilyBound {probe :
  Line.GaussianLine → Fraction.Rational}
    (data : Chordal.Probe.ProbeVarianceData probe)
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness) :
    Data.Rat.Interval :=
  CCL.Prefix.extendedPrefixFamilyProbeVarianceBound distribution suffix
    extendedRealizes probe data.meanFactor data.meanFactorNonnegative
    data.meanSensitive data.squareFactor data.squareFactorNonnegative
    data.squareSensitive

/-- The variance-data enclosure after prefix extension refines its original family enclosure. -/
theorem extendedPrefixFamilyBound_refines {probe :
  Line.GaussianLine → Fraction.Rational}
    (data : Chordal.Probe.ProbeVarianceData probe)
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness) :
    Interval.Refines
      (data.extendedPrefixFamilyBound distribution suffix extendedRealizes)
      (data.prefixFamilyBound distribution) :=
  CCL.Prefix.extendedPrefixFamilyProbeVarianceBound_refines distribution suffix
    extendedRealizes probe data.meanFactor data.meanFactorNonnegative
    data.meanSensitive data.squareFactor data.squareFactorNonnegative
    data.squareSensitive

end

end ProbeVarianceData
end Purelib.Geometry.Projective.Chordal.Probe

end

end
