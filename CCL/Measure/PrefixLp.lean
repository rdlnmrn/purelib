import CCL.Measure.PrefixProcess
import FiniteMeasure.NaturalLp

/-!
# Powered-Lp observations from finite CCL prefixes

A rational probe of a projective CCL realization can be raised to any
displayed natural-powered magnitude.  When that transformed probe carries an
explicit chordal sensitivity bound, the existing finite-cylinder machinery
gives a certified rational enclosure of its finite powered-Lp expectation.
No eventual decoded point or infinite stream is selected.
-/

namespace CCL.FiniteMeasure

/-- The transformed projective probe whose finite expectation is the
powered-Lp quantity of the original rational probe. -/
def poweredProbe (probe : Proj → Coordinate) (exponent : Nat) :
    Proj → Coordinate :=
  fun point =>
    _root_.FiniteMeasure.rationalSeparation (probe point) 0 ^ exponent

/-- Propagate a finite probability table of CCL prefix certificates through
one natural-powered rational probe. -/
def prefixFamilyProbePoweredLpBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  prefixFamilyProbeExpectationBound distribution
    (poweredProbe probe exponent) factor factorNonnegative sensitive

/-- The powered-Lp enclosure uncertainty is the exact finite expectation of
the displayed per-cylinder spread budgets. -/
theorem prefixFamilyProbePoweredLpBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * cylinderSpread certificate.blocks) :=
  prefixFamilyProbeExpectationBound_width distribution
    (poweredProbe probe exponent) factor factorNonnegative sensitive

/-- Every explicitly supplied realization family has its exact finite
powered-Lp value inside the CCL-derived rational enclosure. -/
theorem prefixFamilyProbePoweredLpBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorNonnegative sensitive).Contains
        (distribution.poweredLp exponent fun certificate =>
          probe (points certificate)) := by
  change (prefixFamilyProbeExpectationBound distribution
      (poweredProbe probe exponent) factor factorNonnegative sensitive).Contains
    (distribution.expectation fun certificate =>
      poweredProbe probe exponent (points certificate))
  exact prefixFamilyProbeExpectationBound_contains distribution
    (poweredProbe probe exponent) factor factorNonnegative sensitive
    points pointsRealize

/-- Appending a finite CCL suffix to every row narrows the complete powered-Lp
enclosure. -/
theorem extendedPrefixFamilyProbePoweredLpBound_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (extendedPrefixFamilyProbeExpectationBound distribution suffix
        extendedRealizes (poweredProbe probe exponent) factor
          factorNonnegative sensitive)
      (prefixFamilyProbePoweredLpBound distribution probe exponent factor
        factorNonnegative sensitive) :=
  extendedPrefixFamilyProbeExpectationBound_refines distribution suffix
    extendedRealizes (poweredProbe probe exponent) factor
      factorNonnegative sensitive

/-- A uniform computable completed-block request makes the powered-Lp
enclosure narrower than the supplied positive rational target. -/
theorem prefixFamilyProbePoweredLpBound_width_lt_requested
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorPositive.le sensitive).width < target :=
  prefixFamilyProbeExpectationBound_width_lt_requested distribution
    (poweredProbe probe exponent) factor factorPositive sensitive target
      targetPositive enough

namespace PrefixFamilyProcess

/-- Progressive finite CCL request process for the powered-Lp value of one
rational probe on a fixed finite probability table. -/
def toProbePoweredLpProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.BoundProcess :=
  process.toProbeExpectationProcess distribution
    (poweredProbe probe exponent) factor factorPositive sensitive

/-- Every explicit realization family remains inside the current progressive
powered-Lp enclosure. -/
theorem poweredLp_mem_toProbePoweredLpProcess_bound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbePoweredLpProcess distribution probe exponent factor
      factorPositive sensitive).bound state).Contains
        (distribution.poweredLp exponent fun item => probe (points item)) := by
  change ((process.toProbeExpectationProcess distribution
      (poweredProbe probe exponent) factor factorPositive sensitive).bound
        state).Contains
    (distribution.expectation fun item =>
      poweredProbe probe exponent (points item))
  exact process.expectation_mem_probeExpectationProcess_bound distribution
    (poweredProbe probe exponent) factor factorPositive sensitive state
      points pointsRealize

/-- One finite rational request makes the progressive powered-Lp enclosure
narrower than the requested tolerance. -/
theorem request_probePoweredLp_width_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbePoweredLpProcess distribution probe exponent factor
      factorPositive sensitive).bound
      ((process.toProbePoweredLpProcess distribution probe exponent factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  process.request_probeExpectation_width_lt distribution
    (poweredProbe probe exponent) factor factorPositive sensitive
      state epsilon positive

end PrefixFamilyProcess

end CCL.FiniteMeasure
