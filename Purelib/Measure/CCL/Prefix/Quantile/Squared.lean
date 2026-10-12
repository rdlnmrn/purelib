module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.CCL.Encoding.Cylinder.Projective
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Quantile.Stability
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Measure.Distribution.Kernel.Basic
import Mathlib.Order.Basic

section
/-!
# Quantile stability from finite squared-sensitive CCL prefixes

Uniform finite CCL cylinder contraction controls executable lower quantiles
of squared-sensitive rational probes.  The result is a direct finite
pushforward theorem at a displayed rational quantile level; no limiting law,
infimum, or completed real value is introduced.
-/

@[expose] public section

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- The retained squared-probe block budget bounds lower-quantile separation between two completed-prefix realizations
by epsilon.

Both laws use the original certificate distribution and the same valid level; the probe's sensitivity factor and
requested epsilon are positive. -/
theorem prefixFamilySquaredProbe_lowerQuantile_separation_le_requested
    (distribution : Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item))
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((distribution.map fun certificate =>
          probe (leftPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun certificate =>
          probe (rightPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  exact (Approximation.CCL.Prefix.realizedSquaredProbe_separation_lt_of_requested
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorPositive sensitive epsilon epsilonPositive
    (enough atom member)).le

/-- The squared-probe block budget bounds lower-quantile separation between two projective-prefix realizations by
epsilon.

Both point families retain projective realization certificates for the exact original atom blocks and use the same level
in `(0, 1]`. -/
theorem projectivePrefixFamilySquaredProbe_lowerQuantile_separation_le_requested
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : Cylinder.CompletedProjectivePrefixCertificate →
      Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item))
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((distribution.map fun certificate =>
          probe (leftPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun certificate =>
          probe (rightPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  exact (Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_separation_lt_of_requested
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorPositive sensitive epsilon epsilonPositive
    (enough atom member)).le

end

namespace PrefixFamilyProcess
end PrefixFamilyProcess
end Purelib.Measure.CCL.Prefix

end
