import CCL.Measure.PrefixProfile
import FiniteMeasure.ThresholdEnclosure

/-!
# Threshold probabilities from finite CCL prefixes

A finite probability table of completed-prefix certificates can be queried
against a rational probe threshold without selecting eventual CCL values.
Rows whose current rational probe bounds lie entirely on one side are decided;
all other rows remain explicitly unresolved.  Their exact rational probability
mass is the complete width of the returned event enclosure.
-/

namespace CCL.FiniteMeasure

/-- Classify every displayed completed-prefix row by comparing its current
rational probe enclosure with one rational threshold. -/
def prefixFamilyThresholdFrontier
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    List (_root_.FiniteMeasure.Classified CompletedPrefixCertificate) :=
  distribution.thresholdFrontier
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    threshold

/-- The lower and upper rational probability sums returned by the current
finite completed-prefix threshold classification. -/
def prefixFamilyThresholdBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) : _root_.FiniteMeasure.Bound :=
  _root_.FiniteMeasure.eventBound
    (prefixFamilyThresholdFrontier distribution probe factor
      factorNonnegative sensitive threshold)

/-- The executable event selecting exactly those prefix rows whose current
probe enclosure still straddles the threshold. -/
def prefixFamilyThresholdUnresolvedEvent
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) : CompletedPrefixCertificate → Bool :=
  _root_.FiniteMeasure.unresolvedStatusEvent fun certificate =>
    _root_.FiniteMeasure.thresholdStatus
      (certificate.probeBound probe factor factorNonnegative sensitive)
      threshold

/-- The threshold-probability enclosure width is exactly the displayed
probability mass of prefix rows that remain unresolved. -/
theorem prefixFamilyThresholdBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    (prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width =
      distribution.probability
        (prefixFamilyThresholdUnresolvedEvent probe factor
          factorNonnegative sensitive threshold) := by
  unfold prefixFamilyThresholdBound prefixFamilyThresholdFrontier
  exact distribution.classifiedEventFrontier_width _

/-- Any explicit choice of realizations for the relevant finite prefix rows
has its exact finite threshold probability inside the computed enclosure. -/
theorem prefixFamilyThresholdBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).Contains
      (distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (points certificate))) := by
  unfold prefixFamilyThresholdBound prefixFamilyThresholdFrontier
  apply distribution.probability_mem_thresholdFrontier
  intro atom member
  exact completedPrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

/-- Classify the same finite rows after appending a supplied finite suffix to
each row's current completed prefix. -/
def extendedPrefixFamilyThresholdFrontier
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
    (threshold : Coordinate) :
    List (_root_.FiniteMeasure.Classified CompletedPrefixCertificate) :=
  distribution.thresholdFrontier
    (fun certificate => completedPrefixProbeBound
      (certificate.blocks ++ suffix certificate) certificate.witness
      (extendedRealizes certificate) probe factor factorNonnegative sensitive)
    threshold

/-- Appending a finite suffix to every displayed prefix row narrows the
complete threshold-probability enclosure. -/
theorem extendedPrefixFamilyThresholdFrontier_refines
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
    (threshold : Coordinate) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.eventBound
        (extendedPrefixFamilyThresholdFrontier distribution suffix
          extendedRealizes probe factor factorNonnegative sensitive threshold))
      (prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive threshold) := by
  unfold extendedPrefixFamilyThresholdFrontier
  unfold prefixFamilyThresholdBound prefixFamilyThresholdFrontier
  apply distribution.thresholdFrontier_eventBound_refines
  intro atom member
  exact completedPrefixProbeBound_append_refines atom.item.blocks
    (suffix atom.item) atom.item.witness (extendedRealizes atom.item)
    probe factor factorNonnegative sensitive

/-- If every displayed prefix probe enclosure lies wholly on one side of the
threshold, the finite threshold-probability enclosure is exact. -/
theorem prefixFamilyThresholdBound_width_eq_zero_of_resolved
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      _root_.FiniteMeasure.ThresholdResolved
        (atom.item.probeBound probe factor factorNonnegative sensitive)
        threshold) :
    (prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width = 0 := by
  unfold prefixFamilyThresholdBound prefixFamilyThresholdFrontier
  exact distribution.thresholdFrontier_width_eq_zero_of_resolved
    (fun certificate => certificate.probeBound probe factor
      factorNonnegative sensitive)
    threshold resolved

/-- A zero-width finite prefix threshold enclosure proves that every two
explicitly admitted realization families have exactly the same threshold
probability. -/
theorem prefixFamilyThresholdProbability_eq_of_width_eq_zero
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item))
    (widthZero : (prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width = 0) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (leftPoints certificate)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun certificate =>
          probe (rightPoints certificate)) := by
  apply _root_.FiniteMeasure.Bound.eq_of_contains_of_contains_of_width_eq_zero
    (prefixFamilyThresholdBound_contains distribution probe factor
      factorNonnegative sensitive threshold leftPoints leftRealize)
    (prefixFamilyThresholdBound_contains distribution probe factor
      factorNonnegative sensitive threshold rightPoints rightRealize)
    widthZero

/-- A direct rational unresolved-mass budget is an accuracy certificate for
the finite threshold probability. -/
theorem prefixFamilyThresholdBound_width_lt_of_unresolved_budget
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold target : Coordinate)
    (budget : distribution.probability
      (prefixFamilyThresholdUnresolvedEvent probe factor
        factorNonnegative sensitive threshold) < target) :
    (prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width < target := by
  rw [prefixFamilyThresholdBound_width]
  exact budget

end CCL.FiniteMeasure
