module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Quantile.Stability
import Purelib.Measure.Weighted.Basic
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

namespace Purelib.Data.CCL.Encoding.Cylinder
namespace PrefixFamilyProcess

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The squared-probe block request bounds lower-quantile separation between two realizations by epsilon.

Both families realize the exact requested prefix state on the original atoms, and the common quantile level lies in `(0,
1]`. -/
theorem request_squaredProbeLowerQuantiles_separation_le
  {index : Type}
    (process : Cylinder.PrefixFamilyProcess index)
    (distribution : Measure.Distribution index)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (state : process.State) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon)
    (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes
        (process.blocks
          (process.request state
            (Budget.requiredSquaredProbeBlockCount epsilon factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes
        (process.blocks
          (process.request state
            (Budget.requiredSquaredProbeBlockCount epsilon factor)) atom.item)
        (rightPoints atom.item))
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((distribution.map fun item => probe (leftPoints item)).lowerQuantile
          level levelPositive levelAtMostOne)
        ((distribution.map fun item => probe (rightPoints item)).lowerQuantile
          level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  exact (Approximation.CCL.Prefix.realizedSquaredProbe_separation_lt_of_requested
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorPositive sensitive epsilon epsilonPositive
    (process.request_length state
      (Budget.requiredSquaredProbeBlockCount epsilon factor) atom.item)).le

end PrefixFamilyProcess
end Purelib.Data.CCL.Encoding.Cylinder

end
