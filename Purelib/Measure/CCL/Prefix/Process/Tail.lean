module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Lp.Enclosure
import Purelib.Measure.Event.RationalDistance
public import Purelib.Measure.CCL.Prefix.Process.Lp
public import Purelib.Measure.CCL.Prefix.Process.Deviation
import Purelib.Measure.Weighted.Basic
import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Interval.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

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
namespace PrefixFamilyProcess

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Tail probability is bounded by the current powered Lp enclosure's upper endpoint divided by the positive threshold's
power. -/
theorem probe_tailProbability_le_currentPoweredLpUpper_div {ι :
  Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => 0)) ≤
      (((CCL.Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe exponent factor
        factorPositive sensitive).bound state).upper /
        threshold ^ exponent := by
  exact Distribution.tailProbability_le_upper_div_of_poweredLp_mem distribution
    (((CCL.Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe exponent factor
      factorPositive sensitive).bound state)
    exponent threshold thresholdPositive (fun item => probe (points item))
    ((CCL.Prefix.PrefixFamilyProcess.poweredLp_mem_toProbePoweredLpProcess_bound process) distribution
      probe exponent factor factorPositive sensitive state points
      pointsRealize)

/-- Deviation probability about the supplied center is bounded by the current powered-deviation upper endpoint divided
by the threshold's power. -/
theorem
  probe_deviationProbability_le_currentPoweredDeviationUpper_div
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
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => center)) ≤
      ((process.toProbePoweredDeviationProcess distribution probe center
        exponent factor factorPositive sensitive).bound state).upper /
          threshold ^ exponent := by
  exact Distribution.tailProbability_le_upper_div_of_poweredLpDistance_mem distribution
    ((process.toProbePoweredDeviationProcess distribution probe center
      exponent factor factorPositive sensitive).bound state)
    exponent threshold thresholdPositive (fun item => probe (points item))
    (fun _ => center)
    (process.poweredLpDistanceConstant_mem_toProbePoweredDeviationProcess_bound
      distribution probe center exponent factor factorPositive sensitive state
      points pointsRealize)

/-- At the requested state, the tail bound's numerator overestimates the realized powered Lp value by less than epsilon.

The original finite law and positive threshold are retained; the guarantee concerns the numerator's enclosure error
before division by the threshold power. -/
theorem request_probeTail_bound_and_numerator_close {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Function.Rat.poweredProbe probe exponent left)
          (Function.Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (((CCL.Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe exponent factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (points atom.item)) :
    let poweredProcess := (CCL.Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe
      exponent factor factorPositive sensitive
    let requested := poweredProcess.request state epsilon positive
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => 0)) ≤
        (poweredProcess.bound requested).upper / threshold ^ exponent ∧
      (poweredProcess.bound requested).upper -
          distribution.poweredLp exponent (fun item => probe (points item)) <
        epsilon := by
  dsimp only
  let poweredProcess := (CCL.Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe
    exponent factor factorPositive sensitive
  let requested := poweredProcess.request state epsilon positive
  have actualInside : (poweredProcess.bound requested).Contains
      (distribution.poweredLp exponent fun item => probe (points item)) := by
    exact (CCL.Prefix.PrefixFamilyProcess.poweredLp_mem_toProbePoweredLpProcess_bound process) distribution
      probe exponent factor factorPositive sensitive requested points
      pointsRealize
  constructor
  · exact Distribution.tailProbability_le_upper_div_of_poweredLp_mem distribution
      (poweredProcess.bound requested) exponent threshold thresholdPositive
      (fun item => probe (points item)) actualInside
  · have upperInside : (poweredProcess.bound requested).Contains
        (poweredProcess.bound requested).upper :=
      ⟨(poweredProcess.bound requested).valid, le_rfl⟩
    exact (poweredProcess.request_pairwise_difference_lt state epsilon positive
      upperInside actualInside).1

end

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
