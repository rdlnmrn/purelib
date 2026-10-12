module
import Purelib.Measure.Classified.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Data.Rat.Distance.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Measure.CCL.Prefix.Threshold.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Cumulative probabilities from finite CCL prefixes

Negating a rational probe turns the cumulative event `f ≤ t` into the lower
threshold event `-t ≤ -f`.  The existing finite prefix classifier therefore
gives a certified rational enclosure for a cumulative probability at any
displayed rational cut.
-/

@[expose] public section

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Enclose cumulative probe probability by threshold-classifying the negated probe at the negated cut.

The construction retains the original certificate distribution and sensitivity factor, so its upper-cut convention is
probe value at most the cut. -/
def prefixFamilyProbeCumulativeBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) : Data.Rat.Interval :=
  CCL.Prefix.prefixFamilyThresholdBound distribution (Function.Rat.negProbe probe) factor
    factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive) (-threshold)

/-- The cumulative enclosure contains the mapped probe law's cumulative probability for any original-prefix realization.
-/
theorem prefixFamilyProbeCumulativeBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive threshold).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.cumulative threshold) := by
  have inside := CCL.Prefix.prefixFamilyThresholdBound_contains distribution
    (Function.Rat.negProbe probe) factor factorNonnegative
    (Chordal.Probe.negProbe_sensitive probe factor sensitive) (-threshold) points
    pointsRealize
  unfold CCL.Prefix.prefixFamilyProbeCumulativeBound
  unfold Distribution.cumulative
  rw [distribution.map_probability]
  change (CCL.Prefix.prefixFamilyThresholdBound distribution (Function.Rat.negProbe probe) factor
    factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive)
    (-threshold)).Contains
      (distribution.probability
        (fun item => decide (probe (points item) ≤ threshold)))
  rw [distribution.probability_congr
    (fun item => decide (probe (points item) ≤ threshold))
    (Measure.atLeastEvent (-threshold)
      (fun item => Function.Rat.negProbe probe (points item)))
    (fun item =>
      (Event.atLeast_negProbe_negThreshold probe points threshold item).symm)]
  exact inside

/-- Cumulative enclosure width is the unresolved probability for the negated probe and cut. -/
theorem prefixFamilyProbeCumulativeBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive threshold).width =
      distribution.probability
        (CCL.Prefix.prefixFamilyThresholdUnresolvedEvent (Function.Rat.negProbe probe) factor
          factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive)
          (-threshold)) :=
  CCL.Prefix.prefixFamilyThresholdBound_width distribution (Function.Rat.negProbe probe) factor
    factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive) (-threshold)

/-- Raising the cumulative cut cannot decrease the enclosure's lower endpoint. -/
theorem prefixFamilyProbeCumulativeBound_lower_mono
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    {lower upper : CCL.Measure.Coordinate} (order : lower ≤ upper) :
    (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive lower).lower ≤
      (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
        factorNonnegative sensitive upper).lower := by
  unfold CCL.Prefix.prefixFamilyProbeCumulativeBound CCL.Prefix.prefixFamilyThresholdBound
    CCL.Prefix.prefixFamilyThresholdFrontier
  exact distribution.thresholdFrontier_lower_anti
    (fun certificate => certificate.probeBound (Function.Rat.negProbe probe) factor
      factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive))
    (Fraction.Order.Arithmetic.neg_le_neg_direct order)

/-- Raising the cumulative cut cannot decrease the enclosure's upper endpoint. -/
theorem prefixFamilyProbeCumulativeBound_upper_mono
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    {lower upper : CCL.Measure.Coordinate} (order : lower ≤ upper) :
    (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
      factorNonnegative sensitive lower).upper ≤
      (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
        factorNonnegative sensitive upper).upper := by
  unfold CCL.Prefix.prefixFamilyProbeCumulativeBound CCL.Prefix.prefixFamilyThresholdBound
    CCL.Prefix.prefixFamilyThresholdFrontier
  exact distribution.thresholdFrontier_upper_anti
    (fun certificate => certificate.probeBound (Function.Rat.negProbe probe) factor
      factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive))
    (Fraction.Order.Arithmetic.neg_le_neg_direct order)

/-- Classify cumulative events after the retained suffix extensions by negating both probe and cut. -/
def extendedPrefixFamilyProbeCumulativeFrontier
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    List (Measure.Classified Cylinder.CompletedPrefixCertificate) :=
  CCL.Prefix.extendedPrefixFamilyThresholdFrontier distribution suffix extendedRealizes
    (Function.Rat.negProbe probe) factor factorNonnegative
    (Chordal.Probe.negProbe_sensitive probe factor sensitive) (-threshold)

/-- The extended cumulative frontier's event bound refines the original cumulative enclosure. -/
theorem extendedPrefixFamilyProbeCumulativeFrontier_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    Interval.Refines
      (Measure.eventBound
        (CCL.Prefix.extendedPrefixFamilyProbeCumulativeFrontier distribution suffix
          extendedRealizes probe factor factorNonnegative sensitive threshold))
      (CCL.Prefix.prefixFamilyProbeCumulativeBound distribution probe factor
        factorNonnegative sensitive threshold) :=
  CCL.Prefix.extendedPrefixFamilyThresholdFrontier_refines distribution suffix
    extendedRealizes (Function.Rat.negProbe probe) factor factorNonnegative
    (Chordal.Probe.negProbe_sensitive probe factor sensitive) (-threshold)

end

end Purelib.Measure.CCL.Prefix
