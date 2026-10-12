module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
public import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Enclosure
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Powered-Lp observations from finite CCL prefixes

A rational probe of a projective CCL realization can be raised to any
displayed natural-powered magnitude.  When that transformed probe carries an
explicit chordal sensitivity bound, the existing finite-cylinder machinery
gives a certified rational enclosure of its finite powered-Lp expectation.
No eventual decoded point or infinite stream is selected.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Enclose the expected natural power of probe magnitude over the original certificate law.

Sensitivity is supplied for the exact powered probe; no root is extracted from the retained rational powered Lp
quantity. -/
def prefixFamilyProbePoweredLpBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  CCL.Prefix.prefixFamilyProbeExpectationBound distribution
    (Function.Rat.poweredProbe probe exponent) factor factorNonnegative sensitive

/-- The powered Lp enclosure's width is the expected doubled scaled cylinder spread. -/
theorem prefixFamilyProbePoweredLpBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) :=
  CCL.Prefix.prefixFamilyProbeExpectationBound_width distribution
    (Function.Rat.poweredProbe probe exponent) factor factorNonnegative sensitive

/-- The enclosure contains the powered Lp value of any probe family realizing the original certificate blocks. -/
theorem prefixFamilyProbePoweredLpBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorNonnegative sensitive).Contains
        (distribution.poweredLp exponent fun certificate =>
          probe (points certificate)) := by
  change (CCL.Prefix.prefixFamilyProbeExpectationBound distribution
      (Function.Rat.poweredProbe probe exponent) factor factorNonnegative sensitive).Contains
    (distribution.expectation fun certificate =>
      Function.Rat.poweredProbe probe exponent (points certificate))
  exact CCL.Prefix.prefixFamilyProbeExpectationBound_contains distribution
    (Function.Rat.poweredProbe probe exponent) factor factorNonnegative sensitive
    points pointsRealize

/-- Retained suffix extensions refine the powered-probe expectation enclosure. -/
theorem extendedPrefixFamilyProbePoweredLpBound_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (CCL.Prefix.extendedPrefixFamilyProbeExpectationBound distribution suffix
        extendedRealizes (Function.Rat.poweredProbe probe exponent) factor
          factorNonnegative sensitive)
      (prefixFamilyProbePoweredLpBound distribution probe exponent factor
        factorNonnegative sensitive) :=
  CCL.Prefix.extendedPrefixFamilyProbeExpectationBound_refines distribution suffix
    extendedRealizes (Function.Rat.poweredProbe probe exponent) factor
      factorNonnegative sensitive

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested per-atom block count makes the powered Lp enclosure narrower than the positive target. -/
theorem prefixFamilyProbePoweredLpBound_width_lt_requested
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorPositive.le sensitive).width < target :=
  CCL.Prefix.prefixFamilyProbeExpectationBound_width_lt_requested distribution
    (Function.Rat.poweredProbe probe exponent) factor factorPositive sensitive target
      targetPositive enough

end Purelib.Measure.CCL.Prefix

end
