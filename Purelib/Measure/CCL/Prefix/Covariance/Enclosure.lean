module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Geometry.Projective.Chordal.Probe.Variance
public import Purelib.Measure.CCL.Prefix.Variance.Enclosure
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Covariance enclosures from finite CCL prefixes

Three finite variance enclosures, for two rational probes and their sum,
enclose covariance through the exact rational polarization identity.  This
uses only displayed prefix families, rational interval arithmetic, and
finite weighted sums.
-/

namespace Purelib.Measure.CCL.Prefix
namespace ProbeVarianceData
end ProbeVarianceData

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Enclose covariance by half the sum-probe variance enclosure minus the two individual variance enclosures.

The left, right and sum probes retain separate variance certificates over the same completed-prefix distribution. -/
def prefixFamilyProbeCovarianceBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : Chordal.Probe.ProbeVarianceData left)
    (rightData : Chordal.Probe.ProbeVarianceData right)
    (sumData : Chordal.Probe.ProbeVarianceData (Function.Rat.addProbe left right)) :
    Data.Rat.Interval :=
  Interval.scale (1 / 2) (by decide)
    ((sumData.prefixFamilyBound distribution).sub
      (leftData.prefixFamilyBound distribution) |>.sub
        (rightData.prefixFamilyBound distribution))

section
open Purelib.Measure
/-- The polarization enclosure contains the covariance of the two probes on any common retained-prefix realization. -/
theorem prefixFamilyProbeCovarianceBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : Chordal.Probe.ProbeVarianceData left)
    (rightData : Chordal.Probe.ProbeVarianceData right)
    (sumData : Chordal.Probe.ProbeVarianceData (Function.Rat.addProbe left right))
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeCovarianceBound distribution left right leftData
      rightData sumData).Contains
      (distribution.covariance
        (fun certificate => left (points certificate))
        (fun certificate => right (points certificate))) := by
  have sumInside := sumData.prefixFamilyBound_contains distribution points
    pointsRealize
  have leftInside := leftData.prefixFamilyBound_contains distribution points
    pointsRealize
  have rightInside := rightData.prefixFamilyBound_contains distribution points
    pointsRealize
  have differenceInside := Interval.sub_contains
    (Interval.sub_contains sumInside leftInside) rightInside
  have scaled := Interval.scale_contains
    (by decide : (0 : Fraction.Rational) ≤ 1 / 2) differenceInside
  have polarization :=
    distribution.two_mul_covariance_eq_variance_add_sub
      (fun certificate => left (points certificate))
      (fun certificate => right (points certificate))
  have covarianceIdentity :
      (1 / 2 : Fraction.Rational) *
          (distribution.variance
              (fun certificate => Function.Rat.addProbe left right (points certificate)) -
            distribution.variance
              (fun certificate => left (points certificate)) -
            distribution.variance
              (fun certificate => right (points certificate))) =
        distribution.covariance
          (fun certificate => left (points certificate))
          (fun certificate => right (points certificate)) := by
    unfold Function.Rat.addProbe
    rw [← polarization]
    have halfTwice : (1 / 2 : Fraction.Rational) * 2 = 1 := by
      decide
    calc
      (1 / 2 : Fraction.Rational) *
          (2 * distribution.covariance
            (fun certificate => left (points certificate))
            (fun certificate => right (points certificate))) =
        ((1 / 2 : Fraction.Rational) * 2) *
          distribution.covariance
            (fun certificate => left (points certificate))
            (fun certificate => right (points certificate)) := by ring1
      _ = distribution.covariance
          (fun certificate => left (points certificate))
          (fun certificate => right (points certificate)) := by
        rw [halfTwice]
        ring1
  rw [covarianceIdentity] at scaled
  exact scaled

/-- The covariance enclosure's width is half the sum of the three original variance-enclosure widths. -/
theorem prefixFamilyProbeCovarianceBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : Chordal.Probe.ProbeVarianceData left)
    (rightData : Chordal.Probe.ProbeVarianceData right)
    (sumData : Chordal.Probe.ProbeVarianceData (Function.Rat.addProbe left right)) :
    (prefixFamilyProbeCovarianceBound distribution left right leftData
      rightData sumData).width =
      (1 / 2 : Fraction.Rational) *
        ((sumData.prefixFamilyBound distribution).width +
          (leftData.prefixFamilyBound distribution).width +
          (rightData.prefixFamilyBound distribution).width) := by
  unfold prefixFamilyProbeCovarianceBound
  rw [Interval.scale_width,
    Interval.sub_width,
    Interval.sub_width]

end

/-- Apply the covariance polarization enclosure to the original distribution after retained suffix extensions. -/
def extendedPrefixFamilyProbeCovarianceBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : Chordal.Probe.ProbeVarianceData left)
    (rightData : Chordal.Probe.ProbeVarianceData right)
    (sumData : Chordal.Probe.ProbeVarianceData (Function.Rat.addProbe left right)) :
    Data.Rat.Interval :=
  Interval.scale (1 / 2) (by decide)
    ((sumData.extendedPrefixFamilyBound distribution suffix extendedRealizes).sub
      (leftData.extendedPrefixFamilyBound distribution suffix
        extendedRealizes) |>.sub
      (rightData.extendedPrefixFamilyBound distribution suffix
        extendedRealizes))

open Purelib.Measure in
/-- Extending the same certificate prefixes refines the covariance enclosure from the retained three variance
certificates. -/
theorem extendedPrefixFamilyProbeCovarianceBound_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : Chordal.Probe.ProbeVarianceData left)
    (rightData : Chordal.Probe.ProbeVarianceData right)
    (sumData : Chordal.Probe.ProbeVarianceData (Function.Rat.addProbe left right)) :
    Interval.Refines
      (extendedPrefixFamilyProbeCovarianceBound distribution suffix
        extendedRealizes left right leftData rightData sumData)
      (prefixFamilyProbeCovarianceBound distribution left right leftData
        rightData sumData) := by
  exact Interval.Refines.scale (1 / 2) (by decide)
    (Interval.Refines.sub
      (Interval.Refines.sub
        (sumData.extendedPrefixFamilyBound_refines distribution suffix
          extendedRealizes)
        (leftData.extendedPrefixFamilyBound_refines distribution suffix
          extendedRealizes))
      (rightData.extendedPrefixFamilyBound_refines distribution suffix
        extendedRealizes))

end

end Purelib.Measure.CCL.Prefix

end
