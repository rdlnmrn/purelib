module
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Classified.Threshold
import Purelib.Measure.Event.RationalOrder
public import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Distance.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Measure.Distribution.Enclosure.Threshold
import Purelib.Measure.Classified.Distribution
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Threshold probabilities from finite CCL prefixes

A finite probability table of completed-prefix certificates can be queried
against a rational probe threshold without selecting eventual CCL values.
Rows whose current rational probe bounds lie entirely on one side are decided;
all other rows remain explicitly unresolved.  Their exact rational probability
mass is the complete width of the returned event enclosure.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Classify the original weighted certificates by whether their probe enclosure lies above the threshold.

The frontier retains each certificate occurrence and weight, distinguishing inside, outside and unresolved status from
its exact enclosure. -/
def prefixFamilyThresholdFrontier
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    List (Measure.Classified Cylinder.CompletedPrefixCertificate) :=
  distribution.thresholdFrontier
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    threshold

open Purelib.Measure in
/-- Bound threshold-event probability by the retained classified frontier's inside and unresolved weights. -/
def prefixFamilyThresholdBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) : Data.Rat.Interval :=
  Measure.eventBound
    (CCL.Prefix.prefixFamilyThresholdFrontier distribution probe factor
      factorNonnegative sensitive threshold)

/-- Select certificates whose probe enclosure does not resolve the supplied threshold. -/
def prefixFamilyThresholdUnresolvedEvent
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) : Cylinder.CompletedPrefixCertificate → Bool :=
  Measure.unresolvedStatusEvent fun certificate =>
    Measure.thresholdStatus
      (certificate.probeBound probe factor factorNonnegative sensitive)
      threshold

section
open Purelib.Measure
/-- Threshold-probability enclosure width equals the original probability of unresolved certificates. -/
theorem prefixFamilyThresholdBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width =
      distribution.probability
        (CCL.Prefix.prefixFamilyThresholdUnresolvedEvent probe factor
          factorNonnegative sensitive threshold) := by
  unfold CCL.Prefix.prefixFamilyThresholdBound CCL.Prefix.prefixFamilyThresholdFrontier
  exact distribution.classifiedEventFrontier_width _

/-- The threshold enclosure contains the event probability for any probe family realizing the original blocks. -/
theorem prefixFamilyThresholdBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).Contains
      (distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (points certificate))) := by
  unfold CCL.Prefix.prefixFamilyThresholdBound CCL.Prefix.prefixFamilyThresholdFrontier
  apply distribution.probability_mem_thresholdFrontier
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

end

/-- Classify threshold events after each certificate's supplied suffix extension, retaining the original weighted
occurrences. -/
def extendedPrefixFamilyThresholdFrontier
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    List (Measure.Classified Cylinder.CompletedPrefixCertificate) :=
  distribution.thresholdFrontier
    (fun certificate => Approximation.CCL.Prefix.completedPrefixProbeBound
      (certificate.blocks ++ suffix certificate) certificate.witness
      (extendedRealizes certificate) probe factor factorNonnegative sensitive)
    threshold

open Purelib.Measure
/-- The extended threshold frontier's probability bound refines the original family bound. -/
theorem extendedPrefixFamilyThresholdFrontier_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Data.CCL.Encoding.Block)
    (extendedRealizes : ∀ certificate,
      Cylinder.Basic.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate) :
    Interval.Refines
      (Measure.eventBound
        (CCL.Prefix.extendedPrefixFamilyThresholdFrontier distribution suffix
          extendedRealizes probe factor factorNonnegative sensitive threshold))
      (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive threshold) := by
  unfold CCL.Prefix.extendedPrefixFamilyThresholdFrontier
  unfold CCL.Prefix.prefixFamilyThresholdBound CCL.Prefix.prefixFamilyThresholdFrontier
  apply distribution.thresholdFrontier_eventBound_refines
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_append_refines atom.item.blocks
    (suffix atom.item) atom.item.witness (extendedRealizes atom.item)
    probe factor factorNonnegative sensitive

/-- Resolving the threshold on every original atom makes the probability enclosure have zero width. -/
theorem prefixFamilyThresholdBound_width_eq_zero_of_resolved
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      Measure.ThresholdResolved
        (atom.item.probeBound probe factor factorNonnegative sensitive)
        threshold) :
    (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width = 0 := by
  unfold CCL.Prefix.prefixFamilyThresholdBound CCL.Prefix.prefixFamilyThresholdFrontier
  exact distribution.thresholdFrontier_width_eq_zero_of_resolved
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    threshold resolved

/-- Zero enclosure width forces identical threshold-event probabilities for any two original-prefix realizations. -/
theorem prefixFamilyThresholdProbability_eq_of_width_eq_zero
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : CCL.Measure.Coordinate)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item))
    (widthZero : (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width = 0) :
    distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (leftPoints certificate)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (rightPoints certificate)) := by
  apply Interval.eq_of_contains_of_contains_of_width_eq_zero
    (CCL.Prefix.prefixFamilyThresholdBound_contains distribution probe factor
      factorNonnegative sensitive threshold leftPoints leftRealize)
    (CCL.Prefix.prefixFamilyThresholdBound_contains distribution probe factor
      factorNonnegative sensitive threshold rightPoints rightRealize)
    widthZero

/-- An unresolved-probability budget directly bounds the threshold enclosure's width. -/
theorem prefixFamilyThresholdBound_width_lt_of_unresolved_budget
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold target : CCL.Measure.Coordinate)
    (budget : distribution.probability
      (CCL.Prefix.prefixFamilyThresholdUnresolvedEvent probe factor
        factorNonnegative sensitive threshold) < target) :
    (CCL.Prefix.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width < target := by
  rw [CCL.Prefix.prefixFamilyThresholdBound_width]
  exact budget

end

end Purelib.Measure.CCL.Prefix
