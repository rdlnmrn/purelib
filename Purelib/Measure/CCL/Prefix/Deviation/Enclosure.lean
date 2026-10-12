module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Enclosure
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Centered powered deviations from finite CCL prefixes

Natural-powered rational separation from a displayed center remains an
ordinary rational probe.  An explicit chordal sensitivity certificate for
that transformed probe therefore yields static and progressive finite
enclosures of the exact powered deviation of every supplied realization
family.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Enclose the expected natural power of probe separation from the supplied center.

Sensitivity is required for the exact powered-deviation probe, and the expectation uses the original completed-prefix
certificate law. -/
def prefixFamilyProbePoweredDeviationBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  CCL.Prefix.prefixFamilyProbeExpectationBound distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorNonnegative
      sensitive

/-- The powered-deviation enclosure has width equal to the expected doubled scaled cylinder spread. -/
theorem prefixFamilyProbePoweredDeviationBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) :=
  CCL.Prefix.prefixFamilyProbeExpectationBound_width distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorNonnegative
      sensitive

/-- The powered-deviation enclosure contains the realizing probe family's powered Lp distance to the constant center. -/
theorem prefixFamilyProbePoweredDeviationBound_contains
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
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorNonnegative sensitive).Contains
      (distribution.poweredLpDistance exponent
        (fun certificate => probe (points certificate)) (fun _ => center)) := by
  change (CCL.Prefix.prefixFamilyProbeExpectationBound distribution
      (Function.Rat.poweredDeviationProbe probe center exponent) factor factorNonnegative
        sensitive).Contains
    (distribution.expectation fun certificate =>
      Function.Rat.poweredDeviationProbe probe center exponent (points certificate))
  exact CCL.Prefix.prefixFamilyProbeExpectationBound_contains distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorNonnegative
      sensitive points pointsRealize

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested per-atom block count makes the powered-deviation enclosure narrower than the positive target. -/
theorem prefixFamilyProbePoweredDeviationBound_width_lt_requested
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorPositive.le sensitive).width < target :=
  CCL.Prefix.prefixFamilyProbeExpectationBound_width_lt_requested distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive target targetPositive enough

namespace PrefixFamilyProcess
end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
