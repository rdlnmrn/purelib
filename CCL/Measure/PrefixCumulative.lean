import CCL.Measure.PrefixQuantile

/-!
# Cumulative probabilities from finite CCL prefixes

Negating a rational probe turns the cumulative event `f ≤ t` into the lower
threshold event `-t ≤ -f`.  The existing finite prefix classifier therefore
gives a certified rational enclosure for a cumulative probability at any
displayed rational cut.
-/

namespace CCL.FiniteMeasure

/-- Rational enclosure of the cumulative probability of a CCL probe at one
displayed cut. -/
def prefixFamilyProbeCumulativeBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) : _root_.FiniteMeasure.Bound :=
  prefixFamilyThresholdBound distribution (negProbe probe) factor
    factorNonnegative (negProbe_sensitive probe factor sensitive) (-threshold)

/-- Every displayed realization family has its exact finite cumulative
probability inside the CCL-derived enclosure. -/
theorem prefixFamilyProbeCumulativeBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive threshold).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.cumulative threshold) := by
  have inside := prefixFamilyThresholdBound_contains distribution
    (negProbe probe) factor factorNonnegative
    (negProbe_sensitive probe factor sensitive) (-threshold) points
    pointsRealize
  unfold prefixFamilyProbeCumulativeBound
  unfold _root_.FiniteMeasure.Distribution.cumulative
  rw [distribution.map_probability]
  change (prefixFamilyThresholdBound distribution (negProbe probe) factor
    factorNonnegative (negProbe_sensitive probe factor sensitive)
    (-threshold)).Contains
      (distribution.probability
        (fun item => decide (probe (points item) ≤ threshold)))
  rw [distribution.probability_congr
    (fun item => decide (probe (points item) ≤ threshold))
    (_root_.FiniteMeasure.atLeastEvent (-threshold)
      (fun item => negProbe probe (points item)))
    (fun item =>
      (atLeast_negProbe_negThreshold probe points threshold item).symm)]
  exact inside

/-- Cumulative-probability uncertainty is exactly the mass of prefix rows
whose probe enclosures still straddle the displayed cut. -/
theorem prefixFamilyProbeCumulativeBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    (prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive threshold).width =
      distribution.probability
        (prefixFamilyThresholdUnresolvedEvent (negProbe probe) factor
          factorNonnegative (negProbe_sensitive probe factor sensitive)
          (-threshold)) :=
  prefixFamilyThresholdBound_width distribution (negProbe probe) factor
    factorNonnegative (negProbe_sensitive probe factor sensitive) (-threshold)

/-- The lower endpoint of the finite cumulative enclosure is monotone in
the displayed rational cut. -/
theorem prefixFamilyProbeCumulativeBound_lower_mono
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    {lower upper : Coordinate} (order : lower ≤ upper) :
    (prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive lower).lower ≤
      (prefixFamilyProbeCumulativeBound distribution probe factor
        factorNonnegative sensitive upper).lower := by
  unfold prefixFamilyProbeCumulativeBound prefixFamilyThresholdBound
    prefixFamilyThresholdFrontier
  exact distribution.thresholdFrontier_lower_anti
    (fun certificate => certificate.probeBound (negProbe probe) factor
      factorNonnegative (negProbe_sensitive probe factor sensitive))
    (RFAP.ConstructiveFraction.neg_le_neg_direct order)

/-- The upper endpoint of the finite cumulative enclosure is monotone in
the displayed rational cut. -/
theorem prefixFamilyProbeCumulativeBound_upper_mono
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    {lower upper : Coordinate} (order : lower ≤ upper) :
    (prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive lower).upper ≤
      (prefixFamilyProbeCumulativeBound distribution probe factor
        factorNonnegative sensitive upper).upper := by
  unfold prefixFamilyProbeCumulativeBound prefixFamilyThresholdBound
    prefixFamilyThresholdFrontier
  exact distribution.thresholdFrontier_upper_anti
    (fun certificate => certificate.probeBound (negProbe probe) factor
      factorNonnegative (negProbe_sensitive probe factor sensitive))
    (RFAP.ConstructiveFraction.neg_le_neg_direct order)

/-- Cumulative classification after appending one supplied finite suffix to
every prefix row. -/
def extendedPrefixFamilyProbeCumulativeFrontier
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    List (_root_.FiniteMeasure.Classified CompletedPrefixCertificate) :=
  extendedPrefixFamilyThresholdFrontier distribution suffix extendedRealizes
    (negProbe probe) factor factorNonnegative
    (negProbe_sensitive probe factor sensitive) (-threshold)

/-- Appending finite suffixes narrows the complete cumulative-probability
enclosure. -/
theorem extendedPrefixFamilyProbeCumulativeFrontier_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.eventBound
        (extendedPrefixFamilyProbeCumulativeFrontier distribution suffix
          extendedRealizes probe factor factorNonnegative sensitive threshold))
      (prefixFamilyProbeCumulativeBound distribution probe factor
        factorNonnegative sensitive threshold) :=
  extendedPrefixFamilyThresholdFrontier_refines distribution suffix
    extendedRealizes (negProbe probe) factor factorNonnegative
    (negProbe_sensitive probe factor sensitive) (-threshold)

end CCL.FiniteMeasure
