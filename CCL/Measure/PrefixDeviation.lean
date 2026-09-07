import CCL.Measure.PrefixLp

/-!
# Centered powered deviations from finite CCL prefixes

Natural-powered rational separation from a displayed center remains an
ordinary rational probe.  An explicit chordal sensitivity certificate for
that transformed probe therefore yields static and progressive finite
enclosures of the exact powered deviation of every supplied realization
family.
-/

namespace CCL.FiniteMeasure

/-- Natural-powered rational deviation of a projective probe from one
displayed rational center. -/
def poweredDeviationProbe (probe : Proj → Coordinate) (center : Coordinate)
    (exponent : Nat) : Proj → Coordinate :=
  fun point =>
    _root_.FiniteMeasure.rationalSeparation (probe point) center ^ exponent

/-- Static finite CCL enclosure of a probe's powered distance from a rational
constant observable. -/
def prefixFamilyProbePoweredDeviationBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  prefixFamilyProbeExpectationBound distribution
    (poweredDeviationProbe probe center exponent) factor factorNonnegative
      sensitive

theorem prefixFamilyProbePoweredDeviationBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * cylinderSpread certificate.blocks) :=
  prefixFamilyProbeExpectationBound_width distribution
    (poweredDeviationProbe probe center exponent) factor factorNonnegative
      sensitive

/-- Every supplied realization family has its exact finite powered distance
from the constant center inside the CCL-derived rational enclosure. -/
theorem prefixFamilyProbePoweredDeviationBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorNonnegative sensitive).Contains
      (distribution.poweredLpDistance exponent
        (fun certificate => probe (points certificate)) (fun _ => center)) := by
  change (prefixFamilyProbeExpectationBound distribution
      (poweredDeviationProbe probe center exponent) factor factorNonnegative
        sensitive).Contains
    (distribution.expectation fun certificate =>
      poweredDeviationProbe probe center exponent (points certificate))
  exact prefixFamilyProbeExpectationBound_contains distribution
    (poweredDeviationProbe probe center exponent) factor factorNonnegative
      sensitive points pointsRealize

/-- A uniform computable block request makes the centered powered-deviation
enclosure narrower than any supplied positive rational target. -/
theorem prefixFamilyProbePoweredDeviationBound_width_lt_requested
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorPositive.le sensitive).width < target :=
  prefixFamilyProbeExpectationBound_width_lt_requested distribution
    (poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive target targetPositive enough

namespace PrefixFamilyProcess

/-- Progressive finite CCL enclosure of powered deviation from a rational
center. -/
def toProbePoweredDeviationProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.BoundProcess :=
  process.toProbeExpectationProcess distribution
    (poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive

theorem poweredLpDistanceConstant_mem_toProbePoweredDeviationProcess_bound
    {ι : Type} (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbePoweredDeviationProcess distribution probe center exponent
      factor factorPositive sensitive).bound state).Contains
      (distribution.poweredLpDistance exponent
        (fun item => probe (points item)) (fun _ => center)) := by
  change ((process.toProbeExpectationProcess distribution
      (poweredDeviationProbe probe center exponent) factor factorPositive
        sensitive).bound state).Contains
    (distribution.expectation fun item =>
      poweredDeviationProbe probe center exponent (points item))
  exact process.expectation_mem_probeExpectationProcess_bound distribution
    (poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive state points pointsRealize

theorem request_probePoweredDeviation_width_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbePoweredDeviationProcess distribution probe center exponent
      factor factorPositive sensitive).bound
      ((process.toProbePoweredDeviationProcess distribution probe center
        exponent factor factorPositive sensitive)
        |>.request state epsilon positive)).width < epsilon :=
  process.request_probeExpectation_width_lt distribution
    (poweredDeviationProbe probe center exponent) factor factorPositive
      sensitive state epsilon positive

end PrefixFamilyProcess

end CCL.FiniteMeasure
