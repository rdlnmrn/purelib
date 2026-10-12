module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.Approximation.Bound.Process
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
public import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.CCL.Prefix.Process.Enclosure
import Purelib.Approximation.OneSided.BoundProcess
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Basic

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

namespace Purelib.Data.CCL.Encoding.Cylinder.PrefixFamilyProcess

section PrefixFamilyProcess

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Build an expectation process for the natural power of probe separation from the fixed supplied center.

The original prefix states and witnesses are retained; the positive sensitivity factor controls the exact
powered-deviation probe. -/
def toProbePoweredDeviationProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Approximation.BoundProcess :=
  process.toProbeExpectationProcess distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive

/-- The current process enclosure contains the realizing probe family's powered Lp distance to the constant center. -/
theorem
  poweredLpDistanceConstant_mem_toProbePoweredDeviationProcess_bound
    {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbePoweredDeviationProcess distribution probe center exponent
      factor factorPositive sensitive).bound state).Contains
      (distribution.poweredLpDistance exponent
        (fun item => probe (points item)) (fun _ => center)) := by
  change ((process.toProbeExpectationProcess distribution
      (Function.Rat.poweredDeviationProbe probe center exponent) factor factorPositive
        sensitive).bound state).Contains
    (distribution.expectation fun item =>
      Function.Rat.poweredDeviationProbe probe center exponent (points item))
  exact process.expectation_mem_probeExpectationProcess_bound distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive state points pointsRealize

/-- The requested powered-deviation enclosure is narrower than the positive epsilon. -/
theorem request_probePoweredDeviation_width_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (center : Fraction.Rational) (exponent
      : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredDeviationProbe probe center exponent left)
          (Function.Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((process.toProbePoweredDeviationProcess distribution probe center exponent
      factor factorPositive sensitive).bound
      ((process.toProbePoweredDeviationProcess distribution probe center
        exponent factor factorPositive sensitive)
        |>.request state epsilon positive)).width < epsilon :=
  process.request_probeExpectation_width_lt distribution
    (Function.Rat.poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive state epsilon positive

end

end PrefixFamilyProcess

end Purelib.Data.CCL.Encoding.Cylinder.PrefixFamilyProcess

end
