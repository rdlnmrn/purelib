module
import Purelib.Data.Rat.Fraction
import Purelib.Measure.CCL.Prefix.Process.Covariance
import Purelib.Measure.CCL.Prefix.Process.Variance.Centered
import Purelib.Measure.CCL.Prefix.Process.Lp
import Purelib.Measure.CCL.Prefix.Process.EssentialMaximum
import Purelib.Measure.CCL.Prefix.Process.Enclosure
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Function.Rat.Distance
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.BinaryPrefix.Decision.Basic
import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Chordal.Probe.Variance
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.BinaryPrefix.Averaging
import Purelib.Measure.CCL.Cylinder.Concentration.Linear
import Purelib.Measure.CCL.Prefix.Content
import Purelib.Measure.CCL.Prefix.Coupling
import Purelib.Measure.CCL.Prefix.Covariance.Enclosure
import Purelib.Measure.CCL.Prefix.Cumulative
import Purelib.Measure.CCL.Prefix.Deviation.Enclosure
import Purelib.Measure.CCL.Prefix.Distribution
import Purelib.Measure.CCL.Prefix.Enclosure
import Purelib.Measure.CCL.Prefix.EssentialMaximum
import Purelib.Measure.CCL.Prefix.Interval.Basic
import Purelib.Measure.CCL.Prefix.Lp.Enclosure
import Purelib.Measure.CCL.Prefix.Process.Variance.Data
import Purelib.Measure.CCL.Prefix.Profile
import Purelib.Measure.CCL.Prefix.Quantile
import Purelib.Measure.CCL.Prefix.Stability
import Purelib.Measure.CCL.Prefix.Tail
import Purelib.Measure.CCL.Prefix.Threshold.Basic
import Purelib.Measure.CCL.Prefix.Transport
import Purelib.Measure.CCL.Prefix.Variance.Centered
import Purelib.Measure.CCL.Prefix.Variance.Enclosure
import Purelib.Measure.Classified.Payload

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Classified.Basic
import Purelib.Measure.BinaryPrefix.Decision.Distribution
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.CCL.Prefix.Process.Threshold
import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.BinaryPrefix.Decision.Process

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.BinaryPrefix.Decision.WorkedExamples

open Purelib.Approximation.CCL
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Data.CCL.Encoding
open Purelib.Measure.CCL
open Purelib.Data.Function
open Purelib.Data.List
open Purelib
open Purelib.Examples

/-- The raw decision event accepting exactly the true first-bit branch. -/
def firstBitTrueEvent :
  BinaryPrefix.RawEvent :=
  .branch .empty .full

/-- The first-bit-true event has weight one half. -/
example : firstBitTrueEvent.weight = 1 / 2 := by
  decide

/-- The terminal frontier bounds equal the exact event weight. -/
example :
    Purelib.Measure.eventBound firstBitTrueEvent.terminalFrontier =
      Interval.exact firstBitTrueEvent.weight :=
  firstBitTrueEvent.terminalFrontier_eventBound

/-- The terminal distribution assigns the original event weight to its inside leaves. -/
example :
    firstBitTrueEvent.terminalDistribution.probability
        BinaryPrefix.RawEvent.terminalInside =
      firstBitTrueEvent.weight :=
  firstBitTrueEvent.terminalDistribution_probability_inside

/-- Appending retained encoding blocks decreases both symbolic weight and geometric spread. -/
example (blocks suffix : List Block) :
    (Prefix.prefixProfile (blocks ++ suffix)).symbolicWeight ≤
        (Prefix.prefixProfile blocks).symbolicWeight ∧
      (Prefix.prefixProfile (blocks ++ suffix)).geometricSpread ≤
        (Prefix.prefixProfile blocks).geometricSpread :=
  Prefix.prefixProfile_append_refines blocks suffix

/-- The computed sufficient block count puts both completed-prefix weight and cylinder spread below the positive target.
-/
example (blocks : List Block)
    (target : Fraction.Rational) (positive : 0 < target)
    (enough : Budget.Dyadic.requiredBlockCount target ≤ blocks.length) :
    Prefix.completedPrefixWeight blocks < target ∧
      Cylinder.cylinderSpread blocks < target :=
  Prefix.completedPrefixProfile_lt_requested positive enough

/-- The finite extension content retains the original completed-prefix mass. -/
example (blocks : List Block) (depth : Nat) :
    (Prefix.completedPrefixExtensionContent blocks depth).total =
      Prefix.completedPrefixWeight blocks :=
  Prefix.completedPrefixExtensionContent_total blocks depth

/-- Depth-d extension distributions retain exactly 2^d atoms. -/
example (blocks : List Block) (depth : Nat) :
    (Prefix.completedPrefixExtensionDistribution blocks depth).atoms.length =
      2 ^ depth :=
  Prefix.completedPrefixExtensionDistribution_atoms_length
    blocks depth

/-- Parent pullback preserves the expected value between consecutive extension depths. -/
example (blocks : List Block) (depth : Nat)
    (value : BinaryPrefix.CCLMeasureWord → Fraction.Rational) :
    (Prefix.completedPrefixExtensionDistribution
        blocks (depth + 1)).expectation
          (fun word => value (BinaryPrefix.rawParent word)) =
      (Prefix.completedPrefixExtensionDistribution
        blocks depth).expectation value :=
  Prefix.completedPrefixExtensionDistribution_expectation_parent
    blocks depth value

/-- Ancestor pullback preserves event probabilities across any finite extra depth. -/
example (blocks : List Block) (depth extra : Nat)
    (event : BinaryPrefix.CCLMeasureWord → Bool) :
    (Prefix.completedPrefixExtensionDistribution
        blocks (depth + extra)).probability
          (fun word => event (BinaryPrefix.rawAncestor extra word)) =
      (Prefix.completedPrefixExtensionDistribution
        blocks depth).probability event :=
  Prefix.completedPrefixExtensionDistribution_probability_ancestor
    blocks depth event extra

/-- The retained ancestor-law coupling has zero relation-mismatch probability. -/
example (blocks : List Block) (depth extra : Nat) :
    (Prefix.completedPrefixExtensionAncestorLawCoupling
      blocks depth extra).mismatchProbability
        (BinaryPrefix.rawAncestorRelation extra) = 0 :=
  Prefix.completedPrefixExtensionAncestorLawCoupling_mismatchProbability
    blocks depth extra

/-- Backward averaging preserves the expectation of a finer finite extension distribution. -/
example (blocks : List Block) (depth extra : Nat)
    (value : BinaryPrefix.CCLMeasureWord → Fraction.Rational) :
    (Prefix.completedPrefixExtensionDistribution
        blocks depth).expectation
          (Purelib.Measure.BinaryPrefix.rawBackwardMean extra value) =
      (Prefix.completedPrefixExtensionDistribution
        blocks (depth + extra)).expectation value :=
  Prefix.completedPrefixExtensionDistribution_expectation_backward
    blocks depth value extra

/-- Backward averaging cannot increase the variance of a finite extension observable. -/
example (blocks : List Block) (depth extra : Nat)
    (value : BinaryPrefix.CCLMeasureWord → Fraction.Rational) :
    (Prefix.completedPrefixExtensionDistribution
        blocks depth).variance
          (Purelib.Measure.BinaryPrefix.rawBackwardMean extra value) ≤
      (Prefix.completedPrefixExtensionDistribution
        blocks (depth + extra)).variance value :=
  Prefix.completedPrefixExtensionDistribution_variance_backward
    blocks depth value extra

/-- The finer extension variance splits into expected backward variance and variance of the backward mean. -/
example (blocks : List Block) (depth extra : Nat)
    (value : BinaryPrefix.CCLMeasureWord → Fraction.Rational) :
    (Prefix.completedPrefixExtensionDistribution
        blocks (depth + extra)).variance value =
      (Prefix.completedPrefixExtensionDistribution
        blocks depth).expectation
          (Purelib.Measure.BinaryPrefix.rawBackwardVariance extra value) +
        (Prefix.completedPrefixExtensionDistribution
          blocks depth).variance
            (Purelib.Measure.BinaryPrefix.rawBackwardMean extra value) :=
  Prefix.completedPrefixExtensionDistribution_totalVariance_backward
    blocks depth value extra

/-- The retained sensitive-probe enclosure width is twice sensitivity times cylinder spread. -/
example (blocks : List Block)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (Prefix.completedPrefixProbeBound blocks witness
      witnessRealizes probe factor factorNonnegative sensitive).width =
        2 * (factor * Cylinder.cylinderSpread blocks) :=
  Prefix.completedPrefixProbeBound_width blocks witness
    witnessRealizes probe factor factorNonnegative sensitive

/-- The finite extension expectation enclosure has the same twice-radius width as the original probe enclosure. -/
example (blocks : List Block) (depth : Nat)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (Prefix.completedPrefixProbeExpectationBound
      blocks depth witness witnessRealizes probe factor factorNonnegative
        sensitive).width =
      2 * (factor * Cylinder.cylinderSpread blocks) :=
  Prefix.completedPrefixProbeExpectationBound_width
    blocks depth witness witnessRealizes probe factor factorNonnegative sensitive

/-- The retained probe expectation enclosure contains every supported realization family on the original prefix. -/
example (blocks : List Block) (depth : Nat)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : BinaryPrefix.CCLMeasureWord →
      Line.GaussianLine)
    (pointsRealize : ∀ atom,
      atom ∈ (Prefix.completedPrefixExtensionDistribution
        blocks depth).atoms →
        Cylinder.Basic.Realizes blocks (points atom.item)) :
    (Prefix.completedPrefixProbeExpectationBound
      blocks depth witness witnessRealizes probe factor factorNonnegative
        sensitive).Contains
      ((Prefix.completedPrefixExtensionDistribution
        blocks depth).expectation (fun word => probe (points word))) :=
  Prefix.completedPrefixProbeExpectationBound_contains
    blocks depth witness witnessRealizes probe factor factorNonnegative
      sensitive points pointsRealize

/-- The retained probe enclosure contains every supplied point realizing the original prefix. -/
example (blocks : List Block)
    (witness point : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (pointRealizes : Cylinder.Basic.Realizes blocks point)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (Prefix.completedPrefixProbeBound blocks witness
      witnessRealizes probe factor factorNonnegative sensitive).Contains
        (probe point) :=
  Prefix.completedPrefixProbeBound_contains blocks witness
    witnessRealizes probe factor factorNonnegative sensitive pointRealizes

/-- Extending a realized prefix refines the sensitive-probe enclosure. -/
example (stem suffix : List Block)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes (stem ++ suffix) witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (Prefix.completedPrefixProbeBound
        (stem ++ suffix) witness witnessRealizes
        probe factor factorNonnegative sensitive)
      (Prefix.completedPrefixProbeBound stem witness
        (Cylinder.realizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) :=
  Prefix.completedPrefixProbeBound_append_refines
    stem suffix witness witnessRealizes probe factor factorNonnegative sensitive

/-- A positive sensitivity and sufficient computed block count make the probe enclosure width smaller than the requested
target. -/
example (blocks : List Block)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredProbeBlockCount target factor ≤
      blocks.length) :
    (Prefix.completedPrefixProbeBound blocks witness
      witnessRealizes probe factor factorPositive.le sensitive).width < target :=
  Prefix.completedPrefixProbeBound_width_lt_requested
    witness witnessRealizes probe factor factorPositive sensitive
    target targetPositive enough

/-- The family probe expectation enclosure width equals the expected twice-radius bound over retained prefix
certificates. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (Prefix.prefixFamilyProbeExpectationBound distribution
      probe factor factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor *
          Cylinder.cylinderSpread certificate.blocks) :=
  Prefix.prefixFamilyProbeExpectationBound_width
    distribution probe factor factorNonnegative sensitive

/-- The family expectation enclosure contains the probe expectation of every supported realization family. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyProbeExpectationBound distribution
      probe factor factorNonnegative sensitive).Contains
        (distribution.expectation fun certificate =>
          probe (points certificate)) :=
  Prefix.prefixFamilyProbeExpectationBound_contains
    distribution probe factor factorNonnegative sensitive
      points pointsRealize

/-- Extending each retained prefix while preserving its witness refines the family expectation enclosure. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate →
      List Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (Prefix.extendedPrefixFamilyProbeExpectationBound
        distribution suffix extendedRealizes probe factor
          factorNonnegative sensitive)
      (Prefix.prefixFamilyProbeExpectationBound distribution
        probe factor factorNonnegative sensitive) :=
  Prefix.extendedPrefixFamilyProbeExpectationBound_refines
    distribution suffix extendedRealizes probe factor factorNonnegative
      sensitive

/-- Per-atom requested block budgets make the family probe expectation enclosure width smaller than the positive target.
-/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (Prefix.prefixFamilyProbeExpectationBound distribution
      probe factor factorPositive.le sensitive).width < target :=
  Prefix.prefixFamilyProbeExpectationBound_width_lt_requested
    distribution probe factor factorPositive sensitive target
      targetPositive enough

/-- The threshold probability enclosure width equals the unresolved threshold-event probability. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) :
    (Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width =
      distribution.probability
        (Prefix.prefixFamilyThresholdUnresolvedEvent probe factor
          factorNonnegative sensitive threshold) :=
  Prefix.prefixFamilyThresholdBound_width distribution probe
    factor factorNonnegative sensitive threshold

/-- The retained threshold enclosure contains the threshold probability of every supported realization family. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).Contains
      (distribution.probability
        (Purelib.Measure.atLeastEvent threshold fun certificate => probe (points certificate))) :=
  Prefix.prefixFamilyThresholdBound_contains distribution probe
    factor factorNonnegative sensitive threshold points pointsRealize

/-- The retained interval-event enclosure contains the within-bound probability of every supported realization family.
-/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Interval)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyWithinBoundProbability distribution probe
      factor factorNonnegative sensitive target).Contains
      (distribution.probability
        (Purelib.Measure.withinBoundEvent target fun certificate =>
          probe (points certificate))) :=
  Prefix.prefixFamilyWithinBoundProbability_contains distribution
    probe factor factorNonnegative sensitive target points pointsRealize

/-- The retained cumulative enclosure contains the cumulative probability of the pushed-forward probe law. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyProbeCumulativeBound distribution probe
      factor factorNonnegative sensitive threshold).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.cumulative threshold) :=
  Prefix.prefixFamilyProbeCumulativeBound_contains distribution
    probe factor factorNonnegative sensitive threshold points pointsRealize

/-- The retained lower and upper threshold-mass margins enclose the realized probe median. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (lower upper : Fraction.Rational) (order : lower ≤ upper)
    (lowerMass : (1 / 2 : Fraction.Rational) <
      (Prefix.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (upperMass : (1 / 2 : Fraction.Rational) ≤
      (Prefix.prefixFamilyThresholdBound distribution
        (Rat.negProbe probe) factor factorNonnegative
        (Chordal.Probe.negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Interval.quantileCutBound lower upper order).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.median) :=
  Prefix.prefixFamilyProbeMedian_mem_quantileCutBound distribution
    probe factor factorNonnegative sensitive lower upper order lowerMass
    upperMass points pointsRealize

/-- Extending the retained prefix family refines its classified threshold frontier enclosure. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate →
      List Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) :
    Interval.Refines
      (Purelib.Measure.eventBound
        (Prefix.extendedPrefixFamilyThresholdFrontier
          distribution suffix extendedRealizes probe factor
            factorNonnegative sensitive threshold))
      (Prefix.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive threshold) :=
  Prefix.extendedPrefixFamilyThresholdFrontier_refines
    distribution suffix extendedRealizes probe factor factorNonnegative
      sensitive threshold

/-- A separated finite threshold request resolves all remaining threshold probability width to zero. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((Prefix.PrefixFamilyProcess.toProbeThresholdProcess process) distribution probe factor
      factorPositive
      sensitive threshold margin marginPositive separated).bound
      (((Prefix.PrefixFamilyProcess.toProbeThresholdProcess process) distribution probe factor
        factorPositive sensitive threshold margin marginPositive separated)
        |>.request state epsilon positive)).width = 0 :=
  (Prefix.PrefixFamilyProcess.request_probeThreshold_width_eq_zero process) distribution
    probe factor
    factorPositive sensitive threshold margin marginPositive separated
    state epsilon positive

/-- The separated threshold process enclosure contains the probability of every supported realization at its retained
state. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((Prefix.PrefixFamilyProcess.toProbeThresholdProcess process) distribution probe factor
      factorPositive
      sensitive threshold margin marginPositive separated).bound state).Contains
      (distribution.probability
        (Purelib.Measure.atLeastEvent threshold fun item => probe (points item))) :=
  (Prefix.PrefixFamilyProcess.probability_mem_toProbeThresholdProcess_bound process)
    distribution probe
    factor factorPositive sensitive threshold margin marginPositive separated
    state points pointsRealize

/-- The finite probe expectation process meets each positive requested enclosure width. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  process.request_probeExpectation_width_lt distribution probe factor
    factorPositive sensitive state epsilon positive

/-- The finite probe expectation process enclosure contains every supported realization expectation at its retained
state. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.expectation fun item => probe (points item)) :=
  process.expectation_mem_probeExpectationProcess_bound distribution
    probe factor factorPositive sensitive state points pointsRealize

/-- The powered-Lp probe enclosure width equals the expected twice-radius sensitivity bound. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredProbe probe exponent left)
          (Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (Prefix.prefixFamilyProbePoweredLpBound distribution
      probe exponent factor factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor *
          Cylinder.cylinderSpread certificate.blocks) :=
  Prefix.prefixFamilyProbePoweredLpBound_width distribution
    probe exponent factor factorNonnegative sensitive

/-- The retained powered-Lp upper bound controls the positive-threshold tail probability by the corresponding threshold
power. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredProbe probe exponent left)
          (Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (Purelib.Measure.separationAtLeast threshold
          (fun certificate => probe (points certificate)) (fun _ => 0)) ≤
      (Prefix.prefixFamilyProbePoweredLpBound distribution probe
        exponent factor factorNonnegative sensitive).upper /
          threshold ^ exponent :=
  Prefix.prefixFamilyProbe_tailProbability_le_upper_div
    distribution probe exponent factor factorNonnegative sensitive threshold
    thresholdPositive points pointsRealize

/-- The retained powered-deviation upper bound controls the tail probability around the supplied center. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational) (center : Fraction.Rational)
    (exponent : Nat) (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredDeviationProbe probe center exponent left)
          (Rat.poweredDeviationProbe probe center exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (Purelib.Measure.separationAtLeast threshold
          (fun certificate => probe (points certificate))
          (fun _ => center)) ≤
      (Prefix.prefixFamilyProbePoweredDeviationBound distribution
        probe center exponent factor factorNonnegative sensitive).upper /
          threshold ^ exponent :=
  Prefix.prefixFamilyProbe_deviationProbability_le_upper_div
    distribution probe center exponent factor factorNonnegative sensitive
    threshold thresholdPositive points pointsRealize

/-- Separate mean and square sensitivity bounds give an enclosure of the realized finite probe variance. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (squareFactor : Fraction.Rational) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.squareProbe probe left)
          (Rat.squareProbe probe right) ≤
        squareFactor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyProbeVarianceBound distribution probe
      meanFactor meanFactorNonnegative meanSensitive squareFactor
      squareFactorNonnegative squareSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) :=
  Prefix.prefixFamilyProbeVarianceBound_contains distribution probe
    meanFactor meanFactorNonnegative meanSensitive squareFactor
    squareFactorNonnegative squareSensitive points pointsRealize

/-- The centered-deviation construction encloses realized variance using the same retained witness expectation. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredDeviationProbe probe
            (Prefix.prefixFamilyProbeWitnessExpectation
              distribution probe) 2 left)
          (Rat.poweredDeviationProbe probe
            (Prefix.prefixFamilyProbeWitnessExpectation
              distribution probe) 2 right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyProbeCenteredVarianceBound distribution
      probe meanFactor deviationFactor deviationFactorNonnegative
      deviationSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) :=
  Prefix.prefixFamilyProbeCenteredVarianceBound_contains
    distribution probe meanFactor meanFactorNonnegative meanSensitive
    deviationFactor deviationFactorNonnegative deviationSensitive points
    pointsRealize

/-- Two supported realizations of the same prefix family have probe L1 distance bounded by the expected sensitivity
radius. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (leftPoints rightPoints :
      Cylinder.CompletedPrefixCertificate →
        Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.l1Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * Cylinder.cylinderSpread certificate.blocks :=
  Prefix.prefixFamilyProbe_l1Distance_le distribution probe factor
    factorNonnegative sensitive leftPoints rightPoints leftRealizes
    rightRealizes

/-- The retained coupling between two realized probe laws has transport cost bounded by the expected sensitivity radius.
-/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (leftPoints rightPoints :
      Cylinder.CompletedPrefixCertificate →
        Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item)) :
    (Prefix.prefixFamilyProbeLawCoupling distribution probe
      leftPoints rightPoints).transportCost Distance.rationalSeparation ≤
        distribution.expectation fun certificate =>
          factor * Cylinder.cylinderSpread certificate.blocks :=
  Prefix.prefixFamilyProbeLawCoupling_transportCost_le
    distribution probe factor factorNonnegative sensitive leftPoints
    rightPoints leftRealizes rightRealizes

/-- A probe realized in one cylinder has variance bounded by the square of its sensitivity radius. -/
example {ι : Type} (distribution : Purelib.Measure.Distribution ι)
    (blocks : List Block)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes blocks (points atom.item))
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    distribution.variance (fun item => probe (points item)) ≤
      (factor * Cylinder.cylinderSpread blocks) ^ 2 :=
  Cylinder.realizedProbeVariance_le_radius_sq distribution blocks
    witness witnessRealizes points pointsRealize probe factor
    factorNonnegative sensitive

/-- The requested centered-variance block budget makes the realized probe variance smaller than the positive target. -/
example {ι : Type} (distribution : Purelib.Measure.Distribution ι)
    (blocks : List Block)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes blocks (points atom.item))
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredProbeBlockCount
      (Budget.centeredVarianceMeanTarget target)
        factor ≤ blocks.length) :
    distribution.variance (fun item => probe (points item)) < target :=
  Cylinder.realizedProbeVariance_lt_of_requested distribution blocks
    witness witnessRealizes points pointsRealize probe factor factorPositive
    sensitive target targetPositive enough

/-- Sufficient requested prefix depth makes positive-threshold deviation from the retained witness have probability
zero. -/
example {ι : Type} (distribution : Purelib.Measure.Distribution ι)
    (blocks : List Block)
    (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes blocks (points atom.item))
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (enough : Budget.requiredProbeBlockCount threshold factor ≤
      blocks.length) :
    distribution.probability
        (Purelib.Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 :=
  Cylinder.realizedProbe_deviationProbability_eq_zero_of_requested
    distribution blocks witness witnessRealizes points pointsRealize probe
    factor factorPositive sensitive threshold thresholdPositive enough

/-- The retained left, right and sum variance data enclose the realized finite probe covariance. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (left right : Line.GaussianLine →
      Fraction.Rational)
    (leftData : Chordal.Probe.ProbeVarianceData left)
    (rightData : Chordal.Probe.ProbeVarianceData right)
    (sumData : Chordal.Probe.ProbeVarianceData
      (Rat.addProbe left right))
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyProbeCovarianceBound distribution left right
      leftData rightData sumData).Contains
      (distribution.covariance
        (fun certificate => left (points certificate))
        (fun certificate => right (points certificate))) :=
  Prefix.prefixFamilyProbeCovarianceBound_contains distribution
    left right leftData rightData sumData points pointsRealize

/-- The finite powered-Lp probe process meets every positive requested enclosure width. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredProbe probe exponent left)
          (Rat.poweredProbe probe exponent right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe exponent
      factor
      factorPositive sensitive).bound
      (((Prefix.PrefixFamilyProcess.toProbePoweredLpProcess process) distribution probe exponent
        factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  (Prefix.PrefixFamilyProcess.request_probePoweredLp_width_lt process) distribution probe
    exponent
    factor factorPositive sensitive state epsilon positive

/-- The essential-maximum enclosure width is twice its retained finite radius. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational) (factor : Fraction.Rational) :
    (Prefix.prefixFamilyProbeEssentialMaximumBound
      distribution probe factor).width =
        2 * Prefix.prefixFamilyProbeEssentialMaximumRadius
          distribution factor :=
  Prefix.prefixFamilyProbeEssentialMaximumBound_width
    distribution probe factor

/-- The essential-maximum enclosure contains the realized probe maximum on the positive-mass support. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate →
      Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (Prefix.prefixFamilyProbeEssentialMaximumBound
      distribution probe factor).Contains
        (distribution.essentialMaximumMagnitude fun certificate =>
          probe (points certificate)) :=
  Prefix.prefixFamilyProbeEssentialMaximumBound_contains
    distribution probe factor factorNonnegative sensitive
      points pointsRealize

/-- Per-atom sufficient prefix budgets make the essential-maximum enclosure width smaller than the positive target. -/
example
    (distribution : Purelib.Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 4) factor ≤
        atom.item.blocks.length) :
    (Prefix.prefixFamilyProbeEssentialMaximumBound
      distribution probe factor).width < target :=
  Prefix.prefixFamilyProbeEssentialMaximumBound_width_lt_requested
    distribution probe factor factorPositive sensitive target
      targetPositive enough

/-- The finite essential-maximum process encloses every supported realization at its retained state. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((Prefix.PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.essentialMaximumMagnitude fun item =>
          probe (points item)) :=
  (Prefix.PrefixFamilyProcess.essentialMaximum_mem_toProbeEssentialMaximumProcess_bound
    process)
    distribution probe factor factorPositive sensitive state
      points pointsRealize

/-- The finite essential-maximum process meets every positive requested enclosure width. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((Prefix.PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe factor
      factorPositive sensitive).bound
      (((Prefix.PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe
        factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  (Prefix.PrefixFamilyProcess.request_probeEssentialMaximum_width_lt process) distribution
    probe factor
    factorPositive sensitive state epsilon positive

/-- The finite centered-variance process encloses realized variance using its retained mean and deviation sensitivity
data. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredDeviationProbe probe
            ((Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2
              left)
          (Rat.poweredDeviationProbe probe
            ((Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2
              right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((Prefix.PrefixFamilyProcess.toProbeCenteredVarianceProcess process) distribution probe
      meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound state).Contains
        (distribution.variance fun item => probe (points item)) :=
  (Prefix.PrefixFamilyProcess.variance_mem_toProbeCenteredVarianceProcess_bound process)
    distribution probe
    meanFactor meanFactorPositive meanSensitive deviationFactor
    deviationFactorPositive deviationSensitive state points pointsRealize

/-- The finite centered-variance process meets every positive requested enclosure width. -/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (probe : Line.GaussianLine →
      Fraction.Rational)
    (meanFactor : Fraction.Rational) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        meanFactor * Chordal.Basic.chordalSq left right)
    (deviationFactor : Fraction.Rational) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      Distance.rationalSeparation
          (Rat.poweredDeviationProbe probe
            ((Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2
              left)
          (Rat.poweredDeviationProbe probe
            ((Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2
              right) ≤
        deviationFactor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((Prefix.PrefixFamilyProcess.toProbeCenteredVarianceProcess process) distribution probe
      meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound
      (((Prefix.PrefixFamilyProcess.toProbeCenteredVarianceProcess process) distribution probe
        meanFactor
        meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
        deviationSensitive).request state epsilon positive)).width < epsilon :=
  (Prefix.PrefixFamilyProcess.request_probeCenteredVariance_width_lt process) distribution
    probe meanFactor
    meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
    deviationSensitive state epsilon positive

/-- The covariance process built from retained left, right and sum data meets every positive requested enclosure width.
-/
example {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Purelib.Measure.Distribution ι)
    (left right : Line.GaussianLine →
      Fraction.Rational)
    (leftData : Prefix.ProbeCenteredVarianceProcessData process
      distribution left)
    (rightData : Prefix.ProbeCenteredVarianceProcessData process
      distribution right)
    (sumData : Prefix.ProbeCenteredVarianceProcessData process
      distribution (Rat.addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive)).width < epsilon :=
  process.request_probeCovariance_width_lt distribution left right leftData
    rightData sumData state epsilon positive

end Purelib.Examples.Measure.BinaryPrefix.Decision.WorkedExamples

end
