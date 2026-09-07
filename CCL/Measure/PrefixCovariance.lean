import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixVariance
import FiniteMeasure.CovarianceAlgebra

/-!
# Covariance enclosures from finite CCL prefixes

Three finite variance enclosures, for two rational probes and their sum,
enclose covariance through the exact rational polarization identity.  This
uses only displayed prefix families, rational interval arithmetic, and
finite weighted sums.
-/

namespace CCL.FiniteMeasure

/-- The pointwise sum of two rational probes on projective data. -/
def addProbe (left right : Proj → Coordinate) : Proj → Coordinate :=
  fun point => left point + right point

/-- The finite sensitivity data needed to enclose the variance of one
rational probe from CCL prefixes. -/
structure ProbeVarianceData (probe : Proj → Coordinate) where
  meanFactor : Coordinate
  meanFactorNonnegative : 0 ≤ meanFactor
  meanSensitive : ∀ left right,
    _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
      meanFactor * CCL.Chordal.chordalSq left right
  squareFactor : Coordinate
  squareFactorNonnegative : 0 ≤ squareFactor
  squareSensitive : ∀ left right,
    _root_.FiniteMeasure.rationalSeparation
        (squareProbe probe left) (squareProbe probe right) ≤
      squareFactor * CCL.Chordal.chordalSq left right

namespace ProbeVarianceData

/-- Package the variance enclosure supplied by one probe's sensitivity
data. -/
def prefixFamilyBound {probe : Proj → Coordinate}
    (data : ProbeVarianceData probe)
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate) :
    _root_.FiniteMeasure.Bound :=
  prefixFamilyProbeVarianceBound distribution probe
    data.meanFactor data.meanFactorNonnegative data.meanSensitive
    data.squareFactor data.squareFactorNonnegative data.squareSensitive

/-- Every displayed realization family has its variance in the packaged
probe enclosure. -/
theorem prefixFamilyBound_contains {probe : Proj → Coordinate}
    (data : ProbeVarianceData probe)
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (data.prefixFamilyBound distribution).Contains
      (distribution.variance fun certificate => probe (points certificate)) :=
  prefixFamilyProbeVarianceBound_contains distribution probe
    data.meanFactor data.meanFactorNonnegative data.meanSensitive
    data.squareFactor data.squareFactorNonnegative data.squareSensitive
    points pointsRealize

/-- Package the variance enclosure after one displayed suffix has been
appended to every prefix row. -/
def extendedPrefixFamilyBound {probe : Proj → Coordinate}
    (data : ProbeVarianceData probe)
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness) :
    _root_.FiniteMeasure.Bound :=
  extendedPrefixFamilyProbeVarianceBound distribution suffix
    extendedRealizes probe data.meanFactor data.meanFactorNonnegative
    data.meanSensitive data.squareFactor data.squareFactorNonnegative
    data.squareSensitive

/-- Appending finite suffixes narrows the packaged variance enclosure. -/
theorem extendedPrefixFamilyBound_refines {probe : Proj → Coordinate}
    (data : ProbeVarianceData probe)
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness) :
    _root_.FiniteMeasure.Bound.Refines
      (data.extendedPrefixFamilyBound distribution suffix extendedRealizes)
      (data.prefixFamilyBound distribution) :=
  extendedPrefixFamilyProbeVarianceBound_refines distribution suffix
    extendedRealizes probe data.meanFactor data.meanFactorNonnegative
    data.meanSensitive data.squareFactor data.squareFactorNonnegative
    data.squareSensitive

end ProbeVarianceData

/-- Covariance enclosure obtained by applying rational polarization to the
three supplied variance enclosures. -/
def prefixFamilyProbeCovarianceBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (left right : Proj → Coordinate)
    (leftData : ProbeVarianceData left)
    (rightData : ProbeVarianceData right)
    (sumData : ProbeVarianceData (addProbe left right)) :
    _root_.FiniteMeasure.Bound :=
  _root_.FiniteMeasure.Bound.scale (1 / 2) (by decide)
    ((sumData.prefixFamilyBound distribution).sub
      (leftData.prefixFamilyBound distribution) |>.sub
        (rightData.prefixFamilyBound distribution))

/-- Every displayed realization family has its exact finite covariance
inside the CCL-derived rational enclosure. -/
theorem prefixFamilyProbeCovarianceBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (left right : Proj → Coordinate)
    (leftData : ProbeVarianceData left)
    (rightData : ProbeVarianceData right)
    (sumData : ProbeVarianceData (addProbe left right))
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
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
  have differenceInside := _root_.FiniteMeasure.Bound.sub_contains
    (_root_.FiniteMeasure.Bound.sub_contains sumInside leftInside) rightInside
  have scaled := _root_.FiniteMeasure.Bound.scale_contains
    (by decide : (0 : Coordinate) ≤ 1 / 2) differenceInside
  have polarization :=
    distribution.two_mul_covariance_eq_variance_add_sub
      (fun certificate => left (points certificate))
      (fun certificate => right (points certificate))
  have covarianceIdentity :
      (1 / 2 : Coordinate) *
          (distribution.variance
              (fun certificate => addProbe left right (points certificate)) -
            distribution.variance
              (fun certificate => left (points certificate)) -
            distribution.variance
              (fun certificate => right (points certificate))) =
        distribution.covariance
          (fun certificate => left (points certificate))
          (fun certificate => right (points certificate)) := by
    unfold addProbe
    rw [← polarization]
    have halfTwice : (1 / 2 : Coordinate) * 2 = 1 := by
      decide
    calc
      (1 / 2 : Coordinate) *
          (2 * distribution.covariance
            (fun certificate => left (points certificate))
            (fun certificate => right (points certificate))) =
        ((1 / 2 : Coordinate) * 2) *
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

/-- The covariance-enclosure width is half the sum of the three displayed
variance-enclosure widths. -/
theorem prefixFamilyProbeCovarianceBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (left right : Proj → Coordinate)
    (leftData : ProbeVarianceData left)
    (rightData : ProbeVarianceData right)
    (sumData : ProbeVarianceData (addProbe left right)) :
    (prefixFamilyProbeCovarianceBound distribution left right leftData
      rightData sumData).width =
      (1 / 2 : Coordinate) *
        ((sumData.prefixFamilyBound distribution).width +
          (leftData.prefixFamilyBound distribution).width +
          (rightData.prefixFamilyBound distribution).width) := by
  unfold prefixFamilyProbeCovarianceBound
  rw [_root_.FiniteMeasure.Bound.scale_width,
    _root_.FiniteMeasure.Bound.sub_width,
    _root_.FiniteMeasure.Bound.sub_width]

/-- Covariance enclosure after appending one supplied finite suffix to every
prefix row. -/
def extendedPrefixFamilyProbeCovarianceBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (left right : Proj → Coordinate)
    (leftData : ProbeVarianceData left)
    (rightData : ProbeVarianceData right)
    (sumData : ProbeVarianceData (addProbe left right)) :
    _root_.FiniteMeasure.Bound :=
  _root_.FiniteMeasure.Bound.scale (1 / 2) (by decide)
    ((sumData.extendedPrefixFamilyBound distribution suffix extendedRealizes).sub
      (leftData.extendedPrefixFamilyBound distribution suffix
        extendedRealizes) |>.sub
      (rightData.extendedPrefixFamilyBound distribution suffix
        extendedRealizes))

/-- Appending finite CCL suffixes narrows the complete covariance
enclosure. -/
theorem extendedPrefixFamilyProbeCovarianceBound_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (left right : Proj → Coordinate)
    (leftData : ProbeVarianceData left)
    (rightData : ProbeVarianceData right)
    (sumData : ProbeVarianceData (addProbe left right)) :
    _root_.FiniteMeasure.Bound.Refines
      (extendedPrefixFamilyProbeCovarianceBound distribution suffix
        extendedRealizes left right leftData rightData sumData)
      (prefixFamilyProbeCovarianceBound distribution left right leftData
        rightData sumData) := by
  exact _root_.FiniteMeasure.Bound.Refines.scale (1 / 2) (by decide)
    (_root_.FiniteMeasure.Bound.Refines.sub
      (_root_.FiniteMeasure.Bound.Refines.sub
        (sumData.extendedPrefixFamilyBound_refines distribution suffix
          extendedRealizes)
        (leftData.extendedPrefixFamilyBound_refines distribution suffix
          extendedRealizes))
      (rightData.extendedPrefixFamilyBound_refines distribution suffix
        extendedRealizes))

end CCL.FiniteMeasure
