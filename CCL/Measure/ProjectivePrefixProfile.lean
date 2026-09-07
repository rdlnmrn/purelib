import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixProfile

/-!
# Finite measure bounds for projectively rescaled CCL prefixes

The integral CCL encoder retains arbitrary nonzero homogeneous rescalings at
intermediate decoding stages.  Its certificates therefore use
`ProjectiveRealizes`, rather than the canonical-tail `Realizes` relation used
by the original prefix profile.  This module gives those exact encoder-facing
certificates the same finite observation and rational-enclosure interface.

No projective normalization, representative choice, completed point, or
infinite continuation is introduced.
-/

namespace CCL.FiniteMeasure

/-- Forget a displayed suffix of a projectively rescaled finite realization
certificate.  The retained point is unchanged. -/
def projectiveRealizesPrefix
    {stem suffix : List Block} {point : Proj}
    (realizes : CCL.Cylinder.ProjectiveRealizes (stem ++ suffix) point) :
    CCL.Cylinder.ProjectiveRealizes stem point := by
  induction stem generalizing point with
  | nil =>
      exact .done point realizes.valid
  | cons block remaining inductionHypothesis =>
      cases realizes with
      | step _ tail rest =>
          exact .step block tail (inductionHypothesis rest)

/-- An inhabited completed-prefix cylinder whose realization traces retain
the encoder's exact homogeneous rescalings. -/
def completedProjectivePrefixObservation
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness) :
    _root_.FiniteMeasure.Observation Proj CCL.Chordal.chordalSq where
  Possible point :=
    Nonempty (CCL.Cylinder.ProjectiveRealizes blocks point)
  witness := witness
  witness_possible := ⟨witnessRealizes⟩
  spread := cylinderSpread blocks
  spread_nonnegative := cylinderSpread_nonneg blocks
  pairwise := by
    intro left right leftPossible rightPossible
    rcases leftPossible with ⟨leftRealizes⟩
    rcases rightPossible with ⟨rightRealizes⟩
    exact CCL.Cylinder.ProjectiveRealizes.chordalSq_le_half_pow
      leftRealizes rightRealizes

/-- Appending explicitly supplied projective blocks refines the admitted
finite predicate. -/
theorem completedProjectivePrefixObservation_append_refines
    (stem suffix : List Block) (witness : Proj)
    (witnessRealizes :
      CCL.Cylinder.ProjectiveRealizes (stem ++ suffix) witness) :
    _root_.FiniteMeasure.Observation.Refines
      (completedProjectivePrefixObservation
        (stem ++ suffix) witness witnessRealizes)
      (completedProjectivePrefixObservation stem witness
        (projectiveRealizesPrefix witnessRealizes)) := by
  constructor
  rintro point ⟨pointRealizes⟩
  exact ⟨projectiveRealizesPrefix pointRealizes⟩

/-- Transport an encoder-facing projective prefix observation through a
supplied rational sensitivity estimate. -/
def completedProjectivePrefixProbeObservation
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Observation Coordinate
      _root_.FiniteMeasure.rationalSeparation :=
  (completedProjectivePrefixObservation blocks witness witnessRealizes).map
    probe factor factorNonnegative sensitive

/-- Rational probe enclosure obtained directly from a projectively rescaled
finite encoder certificate. -/
def completedProjectivePrefixProbeBound
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (completedProjectivePrefixProbeObservation blocks witness witnessRealizes
    probe factor factorNonnegative sensitive).rationalBound

/-- Every explicitly supplied projective realization evaluates inside the
encoder-facing rational probe enclosure. -/
theorem completedProjectivePrefixProbeBound_contains
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    {point : Proj}
    (pointRealizes : CCL.Cylinder.ProjectiveRealizes blocks point) :
    (completedProjectivePrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).Contains (probe point) := by
  apply _root_.FiniteMeasure.Observation.rationalBound_contains
  exact ⟨point, ⟨pointRealizes⟩, rfl⟩

/-- The projective-prefix probe enclosure has the same explicit rational
width as its canonical-tail counterpart. -/
theorem completedProjectivePrefixProbeBound_width
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (completedProjectivePrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).width =
        2 * (factor * cylinderSpread blocks) := by
  rw [completedProjectivePrefixProbeBound,
    _root_.FiniteMeasure.Observation.rationalBound_width]
  rfl

/-- Extending an encoder-facing completed prefix gives a nested probe
enclosure when the same projective witness is retained. -/
theorem completedProjectivePrefixProbeBound_append_refines
    (stem suffix : List Block) (witness : Proj)
    (witnessRealizes :
      CCL.Cylinder.ProjectiveRealizes (stem ++ suffix) witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (completedProjectivePrefixProbeBound (stem ++ suffix) witness
        witnessRealizes probe factor factorNonnegative sensitive)
      (completedProjectivePrefixProbeBound stem witness
        (projectiveRealizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) := by
  have spreadLe :
      factor * cylinderSpread (stem ++ suffix) ≤
        factor * cylinderSpread stem :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (cylinderSpread_le_of_append stem suffix) factorNonnegative
  constructor
  · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct spreadLe (probe witness)
  · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl spreadLe

/-- A finite positive rational request can be discharged directly against
the number of completed projective blocks emitted by the encoder. -/
theorem completedProjectivePrefixProbeBound_width_lt_requested
    {blocks : List Block} (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : requiredProbeBlockCount target factor ≤ blocks.length) :
    (completedProjectivePrefixProbeBound blocks witness witnessRealizes
      probe factor factorPositive.le sensitive).width < target := by
  have scalePositive : (0 : Coordinate) < 2 * factor :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) factorPositive
  have spreadTargetPositive :
      (0 : Coordinate) < target / (2 * factor) :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive scalePositive
  have spreadSmall : cylinderSpread blocks < target / (2 * factor) :=
    cylinderSpread_lt_of_requiredBlockCount_le spreadTargetPositive enough
  have scaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      scalePositive spreadSmall
  rw [completedProjectivePrefixProbeBound_width]
  calc
    2 * (factor * cylinderSpread blocks) =
        (2 * factor) * cylinderSpread blocks := by ring1
    _ < (2 * factor) * (target / (2 * factor)) := scaled
    _ = target := by
      calc
        (2 * factor) * (target / (2 * factor)) =
            (target / (2 * factor)) * (2 * factor) := by ring1
        _ = target :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            target (2 * factor) scalePositive.ne'

/-! ## Heterogeneous finite families of encoder-facing certificates -/

/-- One finite completed-prefix certificate preserving the exact projective
rescalings carried by an integral CCL encoder trace. -/
structure CompletedProjectivePrefixCertificate where
  blocks : List Block
  witness : Proj
  witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness

namespace CompletedProjectivePrefixCertificate

/-- The rational probe enclosure supplied by one projective certificate. -/
def probeBound (certificate : CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  completedProjectivePrefixProbeBound certificate.blocks certificate.witness
    certificate.witnessRealizes probe factor factorNonnegative sensitive

end CompletedProjectivePrefixCertificate

/-- Weighted rational expectation enclosure for a finite table of possibly
different projective-prefix certificates. -/
def projectivePrefixFamilyProbeExpectationBound
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  distribution.enclosedExpectation fun certificate =>
    certificate.probeBound probe factor factorNonnegative sensitive

/-- The total width is exactly the finite expected width of the individual
projective-prefix enclosures. -/
theorem projectivePrefixFamilyProbeExpectationBound_width
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * cylinderSpread certificate.blocks) := by
  unfold projectivePrefixFamilyProbeExpectationBound
  rw [_root_.FiniteMeasure.Distribution.enclosedExpectation_width]
  exact distribution.expectation_congr _ _ (fun certificate =>
    completedProjectivePrefixProbeBound_width certificate.blocks
      certificate.witness certificate.witnessRealizes probe factor
      factorNonnegative sensitive)

/-- Every explicitly supplied projective realization family has its exact
finite probe expectation inside the heterogeneous enclosure. -/
theorem projectivePrefixFamilyProbeExpectationBound_contains
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedProjectivePrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (points atom.item)) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).Contains
        (distribution.expectation fun certificate =>
          probe (points certificate)) := by
  unfold projectivePrefixFamilyProbeExpectationBound
  apply _root_.FiniteMeasure.Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact completedProjectivePrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

/-- An explicitly checked finite weighted spread budget proves the requested
strict expectation width without imposing a uniform row precision. -/
theorem projectivePrefixFamilyProbeExpectationBound_width_lt_of_budget
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate)
    (budget : distribution.expectation (fun certificate =>
      2 * (factor * cylinderSpread certificate.blocks)) < target) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width < target := by
  rw [projectivePrefixFamilyProbeExpectationBound_width]
  exact budget

/-- A uniform computed completed-block request makes the heterogeneous
projective-prefix expectation enclosure narrower than the supplied positive
rational tolerance. -/
theorem projectivePrefixFamilyProbeExpectationBound_width_lt_requested
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorPositive.le sensitive).width < target := by
  have halfPositive : (0 : Coordinate) < target / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive (by decide)
  have halfSmall : target / 2 < target := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      (by decide : (0 : Coordinate) < 2)).2
    calc
      target = target * 1 := by ring1
      _ < target * 2 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          targetPositive (by decide)
  unfold projectivePrefixFamilyProbeExpectationBound
  apply distribution.enclosedExpectation_width_lt_of_uniform
    (fun certificate => certificate.probeBound probe factor
      factorPositive.le sensitive)
    (target / 2) target
  · intro atom member
    exact (completedProjectivePrefixProbeBound_width_lt_requested
      atom.item.witness atom.item.witnessRealizes probe factor factorPositive
      sensitive (target / 2) halfPositive (enough atom member)).le
  · exact halfSmall

end CCL.FiniteMeasure
