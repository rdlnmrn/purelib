module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
public import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.CCL.Prefix.Process.Enclosure
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Weighted.Basic
import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Basic

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
namespace PrefixFamilyProcess

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Build an expectation process for the natural power of probe magnitude.

The original prefix states and witnesses remain fixed, with positive sensitivity supplied for the powered probe and
rational powered Lp values retained without extracting roots. -/
def toProbePoweredLpProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Approximation.BoundProcess :=
  process.toProbeExpectationProcess distribution
    (Function.Rat.poweredProbe probe exponent) factor factorPositive sensitive

open Purelib.Measure
/-- The current process enclosure contains the powered Lp value of every realizing probe family. -/
theorem poweredLp_mem_toProbePoweredLpProcess_bound {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((toProbePoweredLpProcess process) distribution probe exponent factor
      factorPositive sensitive).bound state).Contains
        (distribution.poweredLp exponent fun item => probe (points item)) := by
  change ((process.toProbeExpectationProcess distribution
      (Function.Rat.poweredProbe probe exponent) factor factorPositive sensitive).bound
        state).Contains
    (distribution.expectation fun item =>
      Function.Rat.poweredProbe probe exponent (points item))
  exact process.expectation_mem_probeExpectationProcess_bound distribution
    (Function.Rat.poweredProbe probe exponent) factor factorPositive sensitive state
      points pointsRealize

/-- The requested powered Lp enclosure is narrower than the positive epsilon. -/
theorem request_probePoweredLp_width_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((toProbePoweredLpProcess process) distribution probe exponent factor
      factorPositive sensitive).bound
      (((toProbePoweredLpProcess process) distribution probe exponent factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  process.request_probeExpectation_width_lt distribution
    (Function.Rat.poweredProbe probe exponent) factor factorPositive sensitive
      state epsilon positive

end

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
