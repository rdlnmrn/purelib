module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Deviation.Enclosure
public import Purelib.Measure.CCL.Prefix.Lp.Enclosure
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Lp.Enclosure
import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Basic

section
@[expose] public section

/-!
# Finite tail bounds from CCL prefix moments

A CCL-derived enclosure of a natural-powered probe moment gives an explicit
Markov bound for the finite probability that the probe magnitude crosses a
positive rational threshold.  Progressive requests additionally make the
displayed moment upper endpoint arbitrarily close to every explicitly
supplied realization family's exact powered moment.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Tail probability is bounded by the powered Lp enclosure's upper endpoint divided by the positive threshold's power.
-/
theorem prefixFamilyProbe_tailProbability_le_upper_div
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun certificate => probe (points certificate))
          (fun _ => 0)) ≤
      (CCL.Prefix.prefixFamilyProbePoweredLpBound distribution probe exponent factor
        factorNonnegative sensitive).upper / threshold ^ exponent := by
  exact Distribution.tailProbability_le_upper_div_of_poweredLp_mem distribution
    (CCL.Prefix.prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorNonnegative sensitive)
    exponent threshold thresholdPositive
    (fun certificate => probe (points certificate))
    (CCL.Prefix.prefixFamilyProbePoweredLpBound_contains distribution probe exponent
      factor factorNonnegative sensitive points pointsRealize)

/-- Deviation probability about the supplied center is bounded by the powered-deviation upper endpoint divided by the
threshold's power. -/
theorem prefixFamilyProbe_deviationProbability_le_upper_div
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun certificate => probe (points certificate))
          (fun _ => center)) ≤
      (CCL.Prefix.prefixFamilyProbePoweredDeviationBound distribution probe center
        exponent factor factorNonnegative sensitive).upper /
          threshold ^ exponent := by
  exact Distribution.tailProbability_le_upper_div_of_poweredLpDistance_mem distribution
    (CCL.Prefix.prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorNonnegative sensitive)
    exponent threshold thresholdPositive
    (fun certificate => probe (points certificate)) (fun _ => center)
    (CCL.Prefix.prefixFamilyProbePoweredDeviationBound_contains distribution probe center
      exponent factor factorNonnegative sensitive points pointsRealize)

end Purelib.Measure.CCL.Prefix

end
