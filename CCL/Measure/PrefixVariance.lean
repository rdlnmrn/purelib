import CCL.Measure.PrefixProfile
import FiniteMeasure.BoundSquare
import FiniteMeasure.Moments

/-!
# Variance enclosures from finite CCL prefixes

Separate CCL sensitivity certificates for a rational probe and its square
give finite enclosures of the mean and second moment.  Exact constructive
interval squaring and subtraction then enclose the finite variance.  Adding
displayed CCL suffixes narrows the complete variance enclosure.
-/

namespace CCL.FiniteMeasure

/-- Squared rational probe used for the second-moment enclosure. -/
def squareProbe (probe : Proj → Coordinate) : Proj → Coordinate :=
  fun point => probe point ^ 2

/-- Variance enclosure obtained from an enclosed second moment minus the
square of the enclosed mean. -/
def prefixFamilyProbeVarianceBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (squareFactor : Coordinate) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (squareProbe probe left) (squareProbe probe right) ≤
        squareFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (prefixFamilyProbeExpectationBound distribution (squareProbe probe)
    squareFactor squareFactorNonnegative squareSensitive).sub
  (prefixFamilyProbeExpectationBound distribution probe meanFactor
    meanFactorNonnegative meanSensitive).square

/-- Every explicitly supplied realization family has its exact finite
variance inside the CCL-derived rational enclosure. -/
theorem prefixFamilyProbeVarianceBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (squareFactor : Coordinate) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (squareProbe probe left) (squareProbe probe right) ≤
        squareFactor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeVarianceBound distribution probe meanFactor
      meanFactorNonnegative meanSensitive squareFactor
      squareFactorNonnegative squareSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) := by
  have meanInside := prefixFamilyProbeExpectationBound_contains distribution
    probe meanFactor meanFactorNonnegative meanSensitive points pointsRealize
  have secondInside := prefixFamilyProbeExpectationBound_contains distribution
    (squareProbe probe) squareFactor squareFactorNonnegative squareSensitive
      points pointsRealize
  have meanSquareInside := _root_.FiniteMeasure.Bound.square_contains meanInside
  have differenceInside := _root_.FiniteMeasure.Bound.sub_contains
    secondInside meanSquareInside
  rw [distribution.variance_eq_secondMoment_sub_sq]
  exact differenceInside

/-- The displayed variance-enclosure width is the sum of the second-moment
enclosure width and the squared-mean enclosure width. -/
theorem prefixFamilyProbeVarianceBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (squareFactor : Coordinate) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (squareProbe probe left) (squareProbe probe right) ≤
        squareFactor * CCL.Chordal.chordalSq left right) :
    (prefixFamilyProbeVarianceBound distribution probe meanFactor
      meanFactorNonnegative meanSensitive squareFactor
      squareFactorNonnegative squareSensitive).width =
      (prefixFamilyProbeExpectationBound distribution (squareProbe probe)
        squareFactor squareFactorNonnegative squareSensitive).width +
      (prefixFamilyProbeExpectationBound distribution probe meanFactor
        meanFactorNonnegative meanSensitive).square.width := by
  unfold prefixFamilyProbeVarianceBound
  exact _root_.FiniteMeasure.Bound.sub_width _ _

/-- Variance enclosure after appending one supplied finite CCL suffix to
every row. -/
def extendedPrefixFamilyProbeVarianceBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (squareFactor : Coordinate) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (squareProbe probe left) (squareProbe probe right) ≤
        squareFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (extendedPrefixFamilyProbeExpectationBound distribution suffix
    extendedRealizes (squareProbe probe) squareFactor
      squareFactorNonnegative squareSensitive).sub
  (extendedPrefixFamilyProbeExpectationBound distribution suffix
    extendedRealizes probe meanFactor meanFactorNonnegative
      meanSensitive).square

/-- Appending finite CCL suffixes narrows the complete variance enclosure. -/
theorem extendedPrefixFamilyProbeVarianceBound_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (squareFactor : Coordinate) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (squareProbe probe left) (squareProbe probe right) ≤
        squareFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (extendedPrefixFamilyProbeVarianceBound distribution suffix
        extendedRealizes probe meanFactor meanFactorNonnegative meanSensitive
        squareFactor squareFactorNonnegative squareSensitive)
      (prefixFamilyProbeVarianceBound distribution probe meanFactor
        meanFactorNonnegative meanSensitive squareFactor
        squareFactorNonnegative squareSensitive) := by
  apply _root_.FiniteMeasure.Bound.Refines.sub
  · exact extendedPrefixFamilyProbeExpectationBound_refines distribution
      suffix extendedRealizes (squareProbe probe) squareFactor
      squareFactorNonnegative squareSensitive
  · exact (extendedPrefixFamilyProbeExpectationBound_refines distribution
      suffix extendedRealizes probe meanFactor meanFactorNonnegative
      meanSensitive).square

end CCL.FiniteMeasure
