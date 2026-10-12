module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Threshold.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.Median.Basic
import Purelib.Measure.Distribution.Quantile.Bounds
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Quantile.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

@[expose] public section

namespace Purelib.Measure.CCL.Prefix

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- A certified upper-tail mass greater than one minus the level places the lower cut below the realizing lower
quantile.

The level lies in `(0, 1]`, and the mass certificate comes from the original prefix family's threshold enclosure. -/
theorem prefixFamilyProbeLowerCut_le_lowerQuantile
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (lower : Fraction.Rational)
    (lowerMass : 1 - level <
      (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    lower ≤ ((distribution.map fun certificate => probe (points certificate))
      |>.lowerQuantile level levelPositive levelAtMostOne) := by
  let observed := distribution.map fun certificate => probe (points certificate)
  let quantile := observed.lowerQuantile level levelPositive levelAtMostOne
  change lower ≤ quantile
  have lowerTailInside := CCL.Prefix.prefixFamilyThresholdBound_contains distribution
    probe factor factorNonnegative sensitive lower points pointsRealize
  have oneMinusLevelLtTail :
      1 - level < distribution.probability
        (Measure.atLeastEvent lower fun certificate =>
          probe (points certificate)) :=
    lowerMass.trans_le lowerTailInside.1
  have belowLowerLt :
      distribution.probability
          (fun certificate => decide (probe (points certificate) < lower)) <
        level :=
    Distribution.probability_strictlyBelow_lt_of_one_sub_lt_probability_atLeast
      distribution (fun certificate => probe (points certificate)) level
      lower oneMinusLevelLtTail
  have observedBelowLowerLt :
      observed.probability (Measure.strictlyBelowEvent lower) <
        level := by
    dsimp only [observed]
    rw [distribution.map_probability]
    exact belowLowerLt
  exact Distribution.lower_le_lowerQuantile_of_probability_strictlyBelow_lt observed
    level levelPositive levelAtMostOne lower observedBelowLowerLt

open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Certified cumulative mass at least the level places the realizing lower quantile below the upper cut. -/
theorem prefixFamilyProbeLowerQuantile_le_upperCut
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (upper : Fraction.Rational)
    (upperMass : level ≤
      (CCL.Prefix.prefixFamilyThresholdBound distribution (Function.Rat.negProbe probe) factor
        factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    ((distribution.map fun certificate => probe (points certificate))
        |>.lowerQuantile level levelPositive levelAtMostOne) ≤ upper := by
  let observed := distribution.map fun certificate => probe (points certificate)
  change observed.lowerQuantile level levelPositive levelAtMostOne ≤ upper
  have upperTailInside := CCL.Prefix.prefixFamilyThresholdBound_contains distribution
    (Function.Rat.negProbe probe) factor factorNonnegative
    (Chordal.Probe.negProbe_sensitive probe factor sensitive) (-upper) points pointsRealize
  have levelLeUpperTail : level ≤ distribution.probability
      (Measure.atLeastEvent (-upper) fun certificate =>
        Function.Rat.negProbe probe (points certificate)) :=
    upperMass.trans upperTailInside.1
  have cumulativeEqual : observed.cumulative upper =
      distribution.probability
        (Measure.atLeastEvent (-upper) fun certificate =>
          Function.Rat.negProbe probe (points certificate)) := by
    dsimp only [observed]
    unfold Distribution.cumulative
    rw [distribution.map_probability]
    exact distribution.probability_congr _ _ (fun item =>
      (Event.atLeast_negProbe_negThreshold probe points upper item).symm)
  have levelLeCumulative : level ≤ observed.cumulative upper := by
    rw [cumulativeEqual]
    exact levelLeUpperTail
  exact ((observed.quantileCertificate level levelPositive levelAtMostOne)
    |>.threshold_le_iff_level_le_cumulative upper).2 levelLeCumulative

/-- Retained lower- and upper-mass certificates enclose every realizing law's lower quantile in the ordered cut
interval. -/
theorem prefixFamilyProbeLowerQuantile_mem_quantileCutBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Fraction.Rational) (order : lower ≤ upper)
    (lowerMass : 1 - level <
      (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (upperMass : level ≤
      (CCL.Prefix.prefixFamilyThresholdBound distribution (Function.Rat.negProbe probe) factor
        factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (Interval.quantileCutBound lower upper order).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.lowerQuantile level levelPositive levelAtMostOne) := by
  constructor
  · exact prefixFamilyProbeLowerCut_le_lowerQuantile distribution probe
      factor factorNonnegative sensitive level levelPositive levelAtMostOne
      lower lowerMass points pointsRealize
  · exact prefixFamilyProbeLowerQuantile_le_upperCut distribution probe
      factor factorNonnegative sensitive level levelPositive levelAtMostOne
      upper upperMass points pointsRealize

/-- The retained half-mass cut certificates enclose every realizing probe law's median. -/
theorem prefixFamilyProbeMedian_mem_quantileCutBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (lower upper : Fraction.Rational) (order : lower ≤ upper)
    (lowerMass : (1 / 2 : Fraction.Rational) <
      (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (upperMass : (1 / 2 : Fraction.Rational) ≤
      (CCL.Prefix.prefixFamilyThresholdBound distribution (Function.Rat.negProbe probe) factor
        factorNonnegative (Chordal.Probe.negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (Interval.quantileCutBound lower upper order).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.median) := by
  unfold Distribution.median
  apply prefixFamilyProbeLowerQuantile_mem_quantileCutBound distribution probe
    factor factorNonnegative sensitive (1 / 2) (by decide) (by decide)
    lower upper order
  · simpa only [show (1 : Fraction.Rational) - 1 / 2 = 1 / 2 by decide] using
      lowerMass
  · exact upperMass
  · exact pointsRealize

end Purelib.Measure.CCL.Prefix

end
