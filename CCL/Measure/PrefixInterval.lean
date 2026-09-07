import CCL.Measure.PrefixProfile
import FiniteMeasure.IntervalEventEnclosure

/-!
# Rational interval probabilities from finite CCL prefixes

Each displayed CCL prefix supplies a rational probe enclosure.  Comparing
those enclosures with one rational target interval produces a certified
finite bin-probability enclosure.  Its width is exactly the mass of the rows
that still touch a target boundary, and appended suffixes can only narrow it.
-/

namespace CCL.FiniteMeasure

/-- Classify every displayed prefix row relative to one rational target
interval. -/
def prefixFamilyWithinBoundFrontier
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) :
    List (_root_.FiniteMeasure.Classified CompletedPrefixCertificate) :=
  distribution.withinBoundFrontier
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    target

/-- Lower and upper rational probability sums for membership in one target
interval. -/
def prefixFamilyWithinBoundProbability
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) : _root_.FiniteMeasure.Bound :=
  _root_.FiniteMeasure.eventBound
    (prefixFamilyWithinBoundFrontier distribution probe factor
      factorNonnegative sensitive target)

/-- The event selecting exactly the prefix rows whose current probe
enclosures are unresolved against the target interval. -/
def prefixFamilyWithinBoundUnresolvedEvent
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) :
    CompletedPrefixCertificate → Bool :=
  _root_.FiniteMeasure.withinBoundUnresolvedEvent
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    target

/-- Bin-probability uncertainty is exactly the displayed mass of unresolved
prefix rows. -/
theorem prefixFamilyWithinBoundProbability_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) :
    (prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).width =
      distribution.probability
        (prefixFamilyWithinBoundUnresolvedEvent probe factor
          factorNonnegative sensitive target) := by
  unfold prefixFamilyWithinBoundProbability
  unfold prefixFamilyWithinBoundFrontier
  exact distribution.withinBoundFrontier_width _ target

/-- Every explicitly supplied realization family has its exact finite bin
probability inside the prefix-derived enclosure. -/
theorem prefixFamilyWithinBoundProbability_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).Contains
      (distribution.probability
        (_root_.FiniteMeasure.withinBoundEvent target fun certificate =>
          probe (points certificate))) := by
  unfold prefixFamilyWithinBoundProbability
  unfold prefixFamilyWithinBoundFrontier
  apply distribution.probability_mem_withinBoundFrontier
  intro atom member
  exact completedPrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

/-- Classify the same rows after appending a displayed finite suffix to each
current prefix. -/
def extendedPrefixFamilyWithinBoundFrontier
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) :
    List (_root_.FiniteMeasure.Classified CompletedPrefixCertificate) :=
  distribution.withinBoundFrontier
    (fun certificate => completedPrefixProbeBound
      (certificate.blocks ++ suffix certificate) certificate.witness
      (extendedRealizes certificate) probe factor factorNonnegative sensitive)
    target

/-- Appending finite suffixes narrows the complete bin-probability
enclosure. -/
theorem extendedPrefixFamilyWithinBoundFrontier_refines
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (suffix : CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.eventBound
        (extendedPrefixFamilyWithinBoundFrontier distribution suffix
          extendedRealizes probe factor factorNonnegative sensitive target))
      (prefixFamilyWithinBoundProbability distribution probe factor
        factorNonnegative sensitive target) := by
  unfold extendedPrefixFamilyWithinBoundFrontier
  unfold prefixFamilyWithinBoundProbability prefixFamilyWithinBoundFrontier
  apply distribution.withinBoundFrontier_eventBound_refines
  intro atom member
  exact completedPrefixProbeBound_append_refines atom.item.blocks
    (suffix atom.item) atom.item.witness (extendedRealizes atom.item)
    probe factor factorNonnegative sensitive

/-- If every displayed prefix enclosure is wholly inside or strictly outside
the target interval, the bin probability is exact. -/
theorem prefixFamilyWithinBoundProbability_width_eq_zero_of_resolved
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      _root_.FiniteMeasure.WithinBoundResolved
        (atom.item.probeBound probe factor factorNonnegative sensitive)
        target) :
    (prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).width = 0 := by
  unfold prefixFamilyWithinBoundProbability prefixFamilyWithinBoundFrontier
  exact distribution.withinBoundFrontier_width_eq_zero_of_resolved
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    target resolved

/-- A displayed unresolved-mass budget is an exact accuracy certificate for
the bin probability. -/
theorem prefixFamilyWithinBoundProbability_width_lt_of_unresolved_budget
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : _root_.FiniteMeasure.Bound) (epsilon : Coordinate)
    (budget : distribution.probability
      (prefixFamilyWithinBoundUnresolvedEvent probe factor
        factorNonnegative sensitive target) < epsilon) :
    (prefixFamilyWithinBoundProbability distribution probe factor
      factorNonnegative sensitive target).width < epsilon := by
  rw [prefixFamilyWithinBoundProbability_width]
  exact budget

end CCL.FiniteMeasure
