module
import Purelib.Measure.Classified.Basic
public import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Classified.Interval
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Data.Rat.Distance.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Measure.Distribution.Enclosure.Interval
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Rational interval probabilities from finite CCL prefixes

Each displayed CCL prefix supplies a rational probe enclosure.  Comparing
those enclosures with one rational target interval produces a certified
finite bin-probability enclosure.  Its width is exactly the mass of the rows
that still touch a target boundary, and appended suffixes can only narrow it.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Classify original certificate occurrences by whether their probe enclosure lies within the target interval.

The frontier preserves each occurrence's weight and distinguishes inside, outside and unresolved interval membership. -/
def prefixFamilyWithinBoundFrontier
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval) :
    List (Measure.Classified Cylinder.CompletedPrefixCertificate) :=
  distribution.withinBoundFrontier
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    target

open Purelib.Measure in
/-- Enclose target-interval probability using the retained frontier's inside and unresolved weights. -/
def prefixFamilyWithinBoundProbability
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval) : Data.Rat.Interval :=
  Measure.eventBound
    (CCL.Prefix.prefixFamilyWithinBoundFrontier distribution probe factor
      factorNonnegative sensitive target)

/-- Select certificates whose probe enclosure leaves target-interval membership unresolved. -/
def prefixFamilyWithinBoundUnresolvedEvent
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval) :
    Cylinder.CompletedPrefixCertificate → Bool :=
  Measure.withinBoundUnresolvedEvent
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    target

section
open Purelib.Measure
/-- The interval-event probability enclosure's width is the original unresolved-event probability. -/
theorem prefixFamilyWithinBoundProbability_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval) :
    (CCL.Prefix.prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).width =
      distribution.probability
        (CCL.Prefix.prefixFamilyWithinBoundUnresolvedEvent probe factor
          factorNonnegative sensitive target) := by
  unfold CCL.Prefix.prefixFamilyWithinBoundProbability
  unfold CCL.Prefix.prefixFamilyWithinBoundFrontier
  exact distribution.withinBoundFrontier_width _ target

/-- The interval-event enclosure contains the probability for every probe family realizing the original blocks. -/
theorem prefixFamilyWithinBoundProbability_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (points atom.item)) :
    (CCL.Prefix.prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).Contains
      (distribution.probability
        (Measure.withinBoundEvent target fun certificate =>
          probe (points certificate))) := by
  unfold CCL.Prefix.prefixFamilyWithinBoundProbability
  unfold CCL.Prefix.prefixFamilyWithinBoundFrontier
  apply distribution.probability_mem_withinBoundFrontier
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

end

/-- Classify the target interval after each certificate's retained suffix extension. -/
def extendedPrefixFamilyWithinBoundFrontier
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
    (target : Data.Rat.Interval) :
    List (Measure.Classified Cylinder.CompletedPrefixCertificate) :=
  distribution.withinBoundFrontier
    (fun certificate => Approximation.CCL.Prefix.completedPrefixProbeBound
      (certificate.blocks ++ suffix certificate) certificate.witness
      (extendedRealizes certificate) probe factor factorNonnegative sensitive)
    target

open Purelib.Measure
/-- The extended interval-membership frontier refines the original probability enclosure. -/
theorem extendedPrefixFamilyWithinBoundFrontier_refines
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
    (target : Data.Rat.Interval) :
    Interval.Refines
      (Measure.eventBound
        (CCL.Prefix.extendedPrefixFamilyWithinBoundFrontier distribution suffix
          extendedRealizes probe factor factorNonnegative sensitive target))
      (CCL.Prefix.prefixFamilyWithinBoundProbability distribution probe factor
        factorNonnegative sensitive target) := by
  unfold CCL.Prefix.extendedPrefixFamilyWithinBoundFrontier
  unfold CCL.Prefix.prefixFamilyWithinBoundProbability CCL.Prefix.prefixFamilyWithinBoundFrontier
  apply distribution.withinBoundFrontier_eventBound_refines
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_append_refines atom.item.blocks
    (suffix atom.item) atom.item.witness (extendedRealizes atom.item)
    probe factor factorNonnegative sensitive

/-- Resolving target-interval membership on every atom makes the probability enclosure have zero width. -/
theorem prefixFamilyWithinBoundProbability_width_eq_zero_of_resolved
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      Measure.WithinBoundResolved
        (atom.item.probeBound probe factor factorNonnegative sensitive)
        target) :
    (CCL.Prefix.prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).width = 0 := by
  unfold CCL.Prefix.prefixFamilyWithinBoundProbability CCL.Prefix.prefixFamilyWithinBoundFrontier
  exact distribution.withinBoundFrontier_width_eq_zero_of_resolved
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    target resolved

/-- An unresolved-event probability budget bounds the interval-event enclosure's width. -/
theorem prefixFamilyWithinBoundProbability_width_lt_of_unresolved_budget
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Data.Rat.Interval) (epsilon : CCL.Measure.Coordinate)
    (budget : distribution.probability
      (CCL.Prefix.prefixFamilyWithinBoundUnresolvedEvent probe factor
        factorNonnegative sensitive target) < epsilon) :
    (CCL.Prefix.prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).width < epsilon := by
  rw [CCL.Prefix.prefixFamilyWithinBoundProbability_width]
  exact budget

end

end Purelib.Measure.CCL.Prefix
