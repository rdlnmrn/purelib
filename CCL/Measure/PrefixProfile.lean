import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.Cylinder
import CCL.Measure.FiniteDepth
import CCL.Measure.PrefixAlgebra
import FiniteMeasure.EnclosureObservation
import FiniteMeasure.EnclosedExpectation

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace CCL.FiniteMeasure

/-- Raw words concatenate when completed-block lists concatenate. -/
theorem rawWord_append (stem suffix : List Block) :
    CCL.Cylinder.rawWord (stem ++ suffix) =
      CCL.Cylinder.rawWord stem ++ CCL.Cylinder.rawWord suffix := by
  induction stem with
  | nil => rfl
  | cons block remaining inductionHypothesis =>
      simp only [List.cons_append, CCL.Cylinder.rawWord_cons,
        inductionHypothesis, List.append_assoc]

/-- Fair-bit symbolic weight of the raw word represented by completed
blocks. -/
def completedPrefixWeight (blocks : List Block) : Coordinate :=
  rawPrefixWeight (CCL.Cylinder.rawWord blocks)

/-- Finite raw-bit decision event selected by the displayed completed CCL
block prefix. -/
def completedPrefixEvent (blocks : List Block) : RawEvent :=
  RawEvent.ofPrefix (CCL.Cylinder.rawWord blocks)

/-- A completed-block prefix expanded into all raw continuations at one
displayed finite depth. -/
def completedPrefixExtensionContent (blocks : List Block) (depth : Nat) :
    _root_.FiniteMeasure.FiniteContent Word :=
  rawExtensionContent (CCL.Cylinder.rawWord blocks) depth

/-- Normalized finite extension distribution below a completed-block prefix
at one displayed raw-bit depth. -/
def completedPrefixExtensionDistribution
    (blocks : List Block) (depth : Nat) :
    _root_.FiniteMeasure.Distribution Word :=
  rawExtensionDistribution (CCL.Cylinder.rawWord blocks) depth

theorem completedPrefixExtensionDistribution_atoms_length
    (blocks : List Block) (depth : Nat) :
    (completedPrefixExtensionDistribution blocks depth).atoms.length =
      2 ^ depth :=
  rawExtensionDistribution_atoms_length (CCL.Cylinder.rawWord blocks) depth

/-- Event probabilities in a finite completed-prefix extension table are
exact extension contents divided by the symbolic prefix weight. -/
theorem completedPrefixExtensionDistribution_probability
    (blocks : List Block) (depth : Nat) (event : Word → Bool) :
    (completedPrefixExtensionDistribution blocks depth).probability event =
      (completedPrefixExtensionContent blocks depth).measure event /
        completedPrefixWeight blocks :=
  rawExtensionDistribution_probability
    (CCL.Cylinder.rawWord blocks) depth event

/-- Successive finite extension tables below a completed CCL prefix are
projectively consistent under explicit final-bit truncation. -/
theorem completedPrefixExtensionDistribution_probability_parent
    (blocks : List Block) (depth : Nat) (event : Word → Bool) :
    (completedPrefixExtensionDistribution blocks (depth + 1)).probability
        (fun word => event (rawParent word)) =
      (completedPrefixExtensionDistribution blocks depth).probability event :=
  rawExtensionDistribution_probability_parent
    (CCL.Cylinder.rawWord blocks) depth event

/-- The same successive-depth consistency for rational observables. -/
theorem completedPrefixExtensionDistribution_expectation_parent
    (blocks : List Block) (depth : Nat) (value : Word → Coordinate) :
    (completedPrefixExtensionDistribution blocks (depth + 1)).expectation
        (fun word => value (rawParent word)) =
      (completedPrefixExtensionDistribution blocks depth).expectation value :=
  rawExtensionDistribution_expectation_parent
    (CCL.Cylinder.rawWord blocks) depth value

/-- Completed-prefix probability consistency across any displayed finite
raw-depth gap. -/
theorem completedPrefixExtensionDistribution_probability_ancestor
    (blocks : List Block) (depth : Nat) (event : Word → Bool)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks (depth + extra)).probability
        (fun word => event (rawAncestor extra word)) =
      (completedPrefixExtensionDistribution blocks depth).probability event :=
  rawExtensionDistribution_probability_ancestor
    (CCL.Cylinder.rawWord blocks) depth event extra

/-- Completed-prefix expectation consistency across any displayed finite
raw-depth gap. -/
theorem completedPrefixExtensionDistribution_expectation_ancestor
    (blocks : List Block) (depth : Nat) (value : Word → Coordinate)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks (depth + extra)).expectation
        (fun word => value (rawAncestor extra word)) =
      (completedPrefixExtensionDistribution blocks depth).expectation value :=
  rawExtensionDistribution_expectation_ancestor
    (CCL.Cylinder.rawWord blocks) depth value extra

/-- Explicit zero-mismatch ancestor coupling between two displayed depths
below a completed CCL prefix. -/
def completedPrefixExtensionAncestorLawCoupling
    (blocks : List Block) (depth extra : Nat) :
    _root_.FiniteMeasure.LawCoupling
      (completedPrefixExtensionDistribution blocks (depth + extra))
      (completedPrefixExtensionDistribution blocks depth) :=
  rawExtensionAncestorLawCoupling
    (CCL.Cylinder.rawWord blocks) depth extra

theorem completedPrefixExtensionAncestorLawCoupling_mismatchProbability
    (blocks : List Block) (depth extra : Nat) :
    _root_.FiniteMeasure.LawCoupling.mismatchProbability
        (completedPrefixExtensionAncestorLawCoupling blocks depth extra)
        (rawAncestorRelation extra) = 0 :=
  rawExtensionAncestorLawCoupling_mismatchProbability
    (CCL.Cylinder.rawWord blocks) depth extra

/-- A deep completed-prefix payoff can be folded backward through exactly
the displayed number of raw binary levels without changing its rational
expectation. -/
theorem completedPrefixExtensionDistribution_expectation_backward
    (blocks : List Block) (depth : Nat) (value : Word → Coordinate)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks depth).expectation
        (rawBackwardMean extra value) =
      (completedPrefixExtensionDistribution blocks (depth + extra)).expectation
        value :=
  rawExtensionDistribution_expectation_backward
    (CCL.Cylinder.rawWord blocks) depth value extra

/-- Finite backward averaging on a completed-prefix extension table cannot
increase exact rational variance. -/
theorem completedPrefixExtensionDistribution_variance_backward
    (blocks : List Block) (depth : Nat) (value : Word → Coordinate)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks depth).variance
        (rawBackwardMean extra value) ≤
      (completedPrefixExtensionDistribution blocks (depth + extra)).variance
        value :=
  rawExtensionDistribution_variance_backward
    (CCL.Cylinder.rawWord blocks) depth value extra

/-- Exact residual-variance decomposition for two displayed finite depths
below one completed CCL prefix. -/
theorem completedPrefixExtensionDistribution_totalVariance_backward
    (blocks : List Block) (depth : Nat) (value : Word → Coordinate)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks (depth + extra)).variance
        value =
      (completedPrefixExtensionDistribution blocks depth).expectation
          (rawBackwardVariance extra value) +
        (completedPrefixExtensionDistribution blocks depth).variance
          (rawBackwardMean extra value) :=
  rawExtensionDistribution_totalVariance_backward
    (CCL.Cylinder.rawWord blocks) depth value extra

/-- Every displayed finite continuation frontier conserves the symbolic
weight of its completed-block prefix exactly. -/
theorem completedPrefixExtensionContent_total
    (blocks : List Block) (depth : Nat) :
    (completedPrefixExtensionContent blocks depth).total =
      completedPrefixWeight blocks :=
  rawExtensionContent_total (CCL.Cylinder.rawWord blocks) depth

theorem completedPrefixEvent_weight (blocks : List Block) :
    (completedPrefixEvent blocks).weight = completedPrefixWeight blocks := by
  exact RawEvent.ofPrefix_weight (CCL.Cylinder.rawWord blocks)

theorem completedPrefixEvent_classifies_append (blocks : List Block)
    (suffix : Word) :
    (completedPrefixEvent blocks).classify
        (CCL.Cylinder.rawWord blocks ++ suffix) =
      _root_.FiniteMeasure.Status.inside :=
  RawEvent.ofPrefix_classify_append (CCL.Cylinder.rawWord blocks) suffix

/-- Executing the finite raw event associated with a completed block prefix
returns its exact symbolic weight as a zero-width generic event bound. -/
theorem completedPrefixEvent_eventBound (blocks : List Block) :
    _root_.FiniteMeasure.eventBound
        (completedPrefixEvent blocks).terminalFrontier =
      _root_.FiniteMeasure.Bound.exact (completedPrefixWeight blocks) := by
  rw [RawEvent.terminalFrontier_eventBound,
    completedPrefixEvent_weight]

theorem completedPrefixWeight_nonneg (blocks : List Block) :
    0 ≤ completedPrefixWeight blocks :=
  rawPrefixWeight_nonneg _

theorem completedPrefixWeight_pos (blocks : List Block) :
    0 < completedPrefixWeight blocks :=
  rawPrefixWeight_pos _

theorem completedPrefixWeight_append (stem suffix : List Block) :
    completedPrefixWeight (stem ++ suffix) =
      completedPrefixWeight stem * completedPrefixWeight suffix := by
  simp only [completedPrefixWeight, rawWord_append, rawPrefixWeight_append]

/-- Adding completed blocks cannot increase symbolic fair-bit weight. -/
theorem completedPrefixWeight_le_of_append (stem suffix : List Block) :
    completedPrefixWeight (stem ++ suffix) ≤
      completedPrefixWeight stem := by
  apply rawPrefixWeight_le_of_prefix
  exact ⟨CCL.Cylinder.rawWord suffix, (rawWord_append stem suffix).symm⟩

theorem cylinderSpread_append (stem suffix : List Block) :
    cylinderSpread (stem ++ suffix) =
      cylinderSpread stem * cylinderSpread suffix := by
  simp only [cylinderSpread, List.length_append, pow_add]

/-- Adding completed blocks cannot increase geometric spread. -/
theorem cylinderSpread_le_of_append (stem suffix : List Block) :
    cylinderSpread (stem ++ suffix) ≤ cylinderSpread stem := by
  rw [cylinderSpread_append]
  have suffixLeOne : cylinderSpread suffix ≤ 1 := by
    have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 2)
      (by decide : (1 / 2 : Coordinate) ≤ 1) suffix.length
    simpa only [cylinderSpread, one_pow] using powerBound
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    suffixLeOne (cylinderSpread_nonneg stem)
  simpa only [mul_one] using scaled

/-- The two rational coordinates of a finite completed prefix.  The field
names preserve their different semantics. -/
structure PrefixProfile where
  symbolicWeight : Coordinate
  geometricSpread : Coordinate

/-- Compute the joint finite profile. -/
def prefixProfile (blocks : List Block) : PrefixProfile where
  symbolicWeight := completedPrefixWeight blocks
  geometricSpread := cylinderSpread blocks

/-- Both coordinates improve under a displayed finite extension. -/
theorem prefixProfile_append_refines (stem suffix : List Block) :
    (prefixProfile (stem ++ suffix)).symbolicWeight ≤
        (prefixProfile stem).symbolicWeight ∧
      (prefixProfile (stem ++ suffix)).geometricSpread ≤
        (prefixProfile stem).geometricSpread :=
  ⟨completedPrefixWeight_le_of_append stem suffix,
    cylinderSpread_le_of_append stem suffix⟩

/-- Every completed block contributes at least one raw bit. -/
theorem blocks_length_le_rawWord_length (blocks : List Block) :
    blocks.length ≤ (CCL.Cylinder.rawWord blocks).length := by
  induction blocks with
  | nil => exact le_rfl
  | cons block remaining inductionHypothesis =>
      simp only [List.length_cons, CCL.Cylinder.rawWord_cons,
        List.length_append]
      have oneLeWord : 1 ≤ block.word.length :=
        (by decide : 1 ≤ 4).trans block.word_length_ge_four
      calc
        remaining.length + 1 ≤
            (CCL.Cylinder.rawWord remaining).length + block.word.length :=
          Nat.add_le_add inductionHypothesis oneLeWord
        _ = block.word.length +
            (CCL.Cylinder.rawWord remaining).length := Nat.add_comm _ _

private theorem half_pow_antitone {smaller larger : Nat}
    (order : smaller ≤ larger) :
    (1 / 2 : Coordinate) ^ larger ≤ (1 / 2 : Coordinate) ^ smaller := by
  obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le order
  rw [equal, pow_add]
  have extraLeOne : (1 / 2 : Coordinate) ^ extra ≤ 1 := by
    have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 2)
      (by decide : (1 / 2 : Coordinate) ≤ 1) extra
    simpa only [one_pow] using powerBound
  have prefixNonnegative : 0 ≤ (1 / 2 : Coordinate) ^ smaller :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) smaller
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    extraLeOne prefixNonnegative
  simpa only [mul_one] using scaled

/-- Numerically, the raw symbolic weight is no larger than the canonical
geometric spread.  This inequality follows only from code length and does not
identify the meanings of the two quantities. -/
theorem completedPrefixWeight_le_cylinderSpread (blocks : List Block) :
    completedPrefixWeight blocks ≤ cylinderSpread blocks := by
  exact half_pow_antitone (blocks_length_le_rawWord_length blocks)

/-- A finite geometric request also makes the symbolic completed-prefix
weight small.  The two conclusions still have distinct interpretations. -/
theorem completedPrefixProfile_lt_requested
    {blocks : List Block} {target : Coordinate} (positive : 0 < target)
    (enough : requiredBlockCount target ≤ blocks.length) :
    completedPrefixWeight blocks < target ∧ cylinderSpread blocks < target := by
  have spreadSmall := cylinderSpread_lt_of_requiredBlockCount_le positive enough
  exact ⟨(completedPrefixWeight_le_cylinderSpread blocks).trans_lt spreadSmall,
    spreadSmall⟩

private theorem realizes_valid
    {blocks : List Block} {point : Proj}
    (realizes : CCL.Cylinder.Realizes blocks point) :
    CCL.Chordal.Proj.HasNonzeroCoordinate point := by
  induction realizes with
  | done point valid => exact valid
  | step block tail rest inductionHypothesis =>
      exact CCL.Chordal.Mat2.act_hasNonzeroCoordinate
        block.matrix_det_ne_zero inductionHypothesis

/-- Forget a displayed suffix of a finite realization certificate. -/
def realizesPrefix
    {stem suffix : List Block} {point : Proj}
    (realizes : CCL.Cylinder.Realizes (stem ++ suffix) point) :
    CCL.Cylinder.Realizes stem point := by
  induction stem generalizing point with
  | nil =>
      exact .done point (realizes_valid realizes)
  | cons block remaining inductionHypothesis =>
      cases realizes with
      | step _ tail rest =>
          exact .step block tail (inductionHypothesis rest)

/-- An inhabited finite completed-prefix cylinder as a neutral observation.
The witness and its realization are explicit finite inputs. -/
def completedPrefixObservation
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness) :
    _root_.FiniteMeasure.Observation Proj CCL.Chordal.chordalSq where
  Possible point := Nonempty (CCL.Cylinder.Realizes blocks point)
  witness := witness
  witness_possible := ⟨witnessRealizes⟩
  spread := cylinderSpread blocks
  spread_nonnegative := cylinderSpread_nonneg blocks
  pairwise := by
    intro left right leftPossible rightPossible
    rcases leftPossible with ⟨leftRealizes⟩
    rcases rightPossible with ⟨rightRealizes⟩
    exact CCL.Cylinder.Realizes.chordalSq_le_half_pow
      leftRealizes rightRealizes

/-- A displayed suffix gives genuine predicate refinement between the two
finite observations. -/
theorem completedPrefixObservation_append_refines
    (stem suffix : List Block) (witness : Proj)
    (witnessRealizes :
      CCL.Cylinder.Realizes (stem ++ suffix) witness) :
    _root_.FiniteMeasure.Observation.Refines
      (completedPrefixObservation (stem ++ suffix) witness witnessRealizes)
      (completedPrefixObservation stem witness
        (realizesPrefix witnessRealizes)) := by
  constructor
  rintro point ⟨pointRealizes⟩
  exact ⟨realizesPrefix pointRealizes⟩

/-- Transport a finite completed-prefix observation through a supplied
rational probe.  The sensitivity certificate explicitly relates probe
separation to squared chordal separation on displayed projective points. -/
def completedPrefixProbeObservation
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Observation Coordinate
      _root_.FiniteMeasure.rationalSeparation :=
  (completedPrefixObservation blocks witness witnessRealizes).map
    probe factor factorNonnegative sensitive

/-- A finite CCL prefix therefore gives an explicit rational enclosure for
any supplied rational probe satisfying the displayed sensitivity estimate.
No eventual projective point is selected. -/
def completedPrefixProbeBound
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (completedPrefixProbeObservation blocks witness witnessRealizes
    probe factor factorNonnegative sensitive).rationalBound

/-- Every explicitly supplied realization of the finite prefix evaluates
inside its rational probe enclosure. -/
theorem completedPrefixProbeBound_contains
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    {point : Proj} (pointRealizes : CCL.Cylinder.Realizes blocks point) :
    (completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).Contains (probe point) := by
  apply _root_.FiniteMeasure.Observation.rationalBound_contains
  exact ⟨point, ⟨pointRealizes⟩, rfl⟩

/-- The enclosure width is the explicit twice-sensitivity-times-prefix
spread budget. -/
theorem completedPrefixProbeBound_width
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive).width =
        2 * (factor * cylinderSpread blocks) := by
  rw [completedPrefixProbeBound,
    _root_.FiniteMeasure.Observation.rationalBound_width]
  rfl

/-- Propagate one finite completed-prefix probe enclosure through the exact
finite extension distribution at a displayed raw depth.  The enclosure is
repeated on the finitely displayed rows; no continuation or eventual CCL
point is introduced. -/
def completedPrefixProbeExpectationBound
    (blocks : List Block) (depth : Nat) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (completedPrefixExtensionDistribution blocks depth).enclosedExpectation
    (fun _ => completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive)

/-- Averaging a single common enclosure over a normalized finite extension
table leaves its rational endpoints unchanged. -/
theorem completedPrefixProbeExpectationBound_eq_probeBound
    (blocks : List Block) (depth : Nat) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    completedPrefixProbeExpectationBound blocks depth witness witnessRealizes
        probe factor factorNonnegative sensitive =
      completedPrefixProbeBound blocks witness witnessRealizes
        probe factor factorNonnegative sensitive := by
  unfold completedPrefixProbeExpectationBound
  apply _root_.FiniteMeasure.Bound.ext
  · rw [_root_.FiniteMeasure.Distribution.enclosedExpectation_lower,
      _root_.FiniteMeasure.Distribution.expectation_constant]
  · rw [_root_.FiniteMeasure.Distribution.enclosedExpectation_upper,
      _root_.FiniteMeasure.Distribution.expectation_constant]

/-- Any explicitly displayed choice of prefix realizations has its finite
average probe value inside the propagated expectation enclosure. -/
theorem completedPrefixProbeExpectationBound_contains
    (blocks : List Block) (depth : Nat) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : Word → Proj)
    (pointsRealize : ∀ atom,
      atom ∈ (completedPrefixExtensionDistribution blocks depth).atoms →
        CCL.Cylinder.Realizes blocks (points atom.item)) :
    (completedPrefixProbeExpectationBound blocks depth witness witnessRealizes
      probe factor factorNonnegative sensitive).Contains
        ((completedPrefixExtensionDistribution blocks depth).expectation
          (fun word => probe (points word))) := by
  apply _root_.FiniteMeasure.Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact completedPrefixProbeBound_contains blocks witness witnessRealizes
    probe factor factorNonnegative sensitive (pointsRealize atom member)

theorem completedPrefixProbeExpectationBound_width
    (blocks : List Block) (depth : Nat) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (completedPrefixProbeExpectationBound blocks depth witness witnessRealizes
      probe factor factorNonnegative sensitive).width =
        2 * (factor * cylinderSpread blocks) := by
  rw [completedPrefixProbeExpectationBound_eq_probeBound,
    completedPrefixProbeBound_width]

/-- Extending a completed prefix gives a genuinely nested rational probe
enclosure when the same displayed realization is used as centre. -/
theorem completedPrefixProbeBound_append_refines
    (stem suffix : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes (stem ++ suffix) witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (completedPrefixProbeBound (stem ++ suffix) witness witnessRealizes
        probe factor factorNonnegative sensitive)
      (completedPrefixProbeBound stem witness
        (realizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) := by
  have spreadLe :
      factor * cylinderSpread (stem ++ suffix) ≤
        factor * cylinderSpread stem :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (cylinderSpread_le_of_append stem suffix) factorNonnegative
  constructor
  · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct spreadLe (probe witness)
  · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl spreadLe

/-- The expectation enclosure inherits the genuine nesting of completed CCL
prefix probe enclosures. -/
theorem completedPrefixProbeExpectationBound_append_refines
    (stem suffix : List Block) (depth : Nat) (witness : Proj)
    (witnessRealizes :
      CCL.Cylinder.Realizes (stem ++ suffix) witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (completedPrefixProbeExpectationBound (stem ++ suffix) depth witness
        witnessRealizes probe factor factorNonnegative sensitive)
      (completedPrefixProbeExpectationBound stem depth witness
        (realizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) := by
  rw [completedPrefixProbeExpectationBound_eq_probeBound,
    completedPrefixProbeExpectationBound_eq_probeBound]
  exact completedPrefixProbeBound_append_refines stem suffix witness
    witnessRealizes probe factor factorNonnegative sensitive

/-! ## Finite laws of heterogeneous completed prefixes -/

/-- One entirely finite, inhabited completed-prefix certificate.  A finite
distribution may carry certificates with different prefix lengths, so each
displayed row can retain its own current precision. -/
structure CompletedPrefixCertificate where
  blocks : List Block
  witness : Proj
  witnessRealizes : CCL.Cylinder.Realizes blocks witness

namespace CompletedPrefixCertificate

/-- The rational probe enclosure supplied by this one finite certificate. -/
def probeBound (certificate : CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  completedPrefixProbeBound certificate.blocks certificate.witness
    certificate.witnessRealizes probe factor factorNonnegative sensitive

end CompletedPrefixCertificate

/-- Propagate a finite probability table of possibly different CCL prefixes
through one rational probe.  The result is the weighted rational enclosure
of all explicitly displayed prefix rows. -/
def prefixFamilyProbeExpectationBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  distribution.enclosedExpectation fun certificate =>
    certificate.probeBound probe factor factorNonnegative sensitive

/-- Exact rational centre obtained by evaluating the supplied probe on each
displayed prefix witness and taking the finite weighted expectation. -/
def prefixFamilyProbeWitnessExpectation
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) : Coordinate :=
  distribution.expectation fun certificate => probe certificate.witness

/-- Exact rational radius obtained by averaging the sensitivity-scaled
spread of every displayed prefix row. -/
def prefixFamilyProbeRadius
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (factor : Coordinate) : Coordinate :=
  distribution.expectation fun certificate =>
    factor * cylinderSpread certificate.blocks

theorem prefixFamilyProbeRadius_nonnegative
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor) :
    0 ≤ prefixFamilyProbeRadius distribution factor := by
  apply distribution.expectation_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
    (cylinderSpread_nonneg atom.item.blocks)

/-- The explicit witness-centred rational bound associated with a finite
prefix family. -/
def prefixFamilyProbeWitnessBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) : _root_.FiniteMeasure.Bound where
  lower := prefixFamilyProbeWitnessExpectation distribution probe -
    prefixFamilyProbeRadius distribution factor
  upper := prefixFamilyProbeWitnessExpectation distribution probe +
    prefixFamilyProbeRadius distribution factor
  valid :=
    (sub_le_self _
      (prefixFamilyProbeRadius_nonnegative distribution factor
        factorNonnegative)).trans
      (le_add_of_nonneg_right
        (prefixFamilyProbeRadius_nonnegative distribution factor
          factorNonnegative))

/-- The propagated expectation enclosure is exactly the displayed rational
witness centre plus or minus the expected prefix radius. -/
theorem prefixFamilyProbeExpectationBound_eq_witnessBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    prefixFamilyProbeExpectationBound distribution probe factor
        factorNonnegative sensitive =
      prefixFamilyProbeWitnessBound distribution probe factor
        factorNonnegative := by
  apply _root_.FiniteMeasure.Bound.ext
  · unfold prefixFamilyProbeExpectationBound prefixFamilyProbeWitnessBound
    rw [_root_.FiniteMeasure.Distribution.enclosedExpectation_lower]
    change distribution.expectation (fun certificate =>
        probe certificate.witness -
          factor * cylinderSpread certificate.blocks) = _
    rw [distribution.expectation_sub]
    rfl
  · unfold prefixFamilyProbeExpectationBound prefixFamilyProbeWitnessBound
    rw [_root_.FiniteMeasure.Distribution.enclosedExpectation_upper]
    change distribution.expectation (fun certificate =>
        probe certificate.witness +
          factor * cylinderSpread certificate.blocks) = _
    rw [distribution.expectation_add]
    rfl

/-- The complete expectation-enclosure width is exactly twice its explicit
expected prefix radius. -/
theorem prefixFamilyProbeExpectationBound_width_eq_two_mul_radius
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width =
      2 * prefixFamilyProbeRadius distribution factor := by
  rw [prefixFamilyProbeExpectationBound_eq_witnessBound]
  unfold prefixFamilyProbeWitnessBound _root_.FiniteMeasure.Bound.width
  ring1

/-- The total uncertainty is exactly the finite expected uncertainty of the
individual completed-prefix certificates. -/
theorem prefixFamilyProbeExpectationBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * cylinderSpread certificate.blocks) := by
  unfold prefixFamilyProbeExpectationBound
  rw [_root_.FiniteMeasure.Distribution.enclosedExpectation_width]
  exact distribution.expectation_congr _ _ (fun certificate =>
    completedPrefixProbeBound_width certificate.blocks
      certificate.witness certificate.witnessRealizes probe factor
      factorNonnegative sensitive)

/-- Any explicitly displayed realization chosen for every relevant prefix
row has its exact finite average probe value inside the family enclosure. -/
theorem prefixFamilyProbeExpectationBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).Contains
        (distribution.expectation fun certificate =>
          probe (points certificate)) := by
  unfold prefixFamilyProbeExpectationBound
  apply _root_.FiniteMeasure.Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact completedPrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

/-- Simultaneously append a displayed finite suffix to every prefix row,
retaining each row's supplied witness. -/
def extendedPrefixFamilyProbeExpectationBound
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
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  distribution.enclosedExpectation fun certificate =>
    completedPrefixProbeBound
      (certificate.blocks ++ suffix certificate) certificate.witness
      (extendedRealizes certificate) probe factor factorNonnegative sensitive

/-- Every realization family of the appended prefixes has its exact finite
probe expectation inside the refined family enclosure. -/
theorem extendedPrefixFamilyProbeExpectationBound_contains
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
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (atom.item.blocks ++ suffix atom.item) (points atom.item)) :
    (extendedPrefixFamilyProbeExpectationBound distribution suffix
      extendedRealizes probe factor factorNonnegative sensitive).Contains
      (distribution.expectation fun certificate => probe (points certificate)) := by
  unfold extendedPrefixFamilyProbeExpectationBound
  apply _root_.FiniteMeasure.Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact completedPrefixProbeBound_contains
    (atom.item.blocks ++ suffix atom.item) atom.item.witness
    (extendedRealizes atom.item) probe factor factorNonnegative sensitive
    (pointsRealize atom member)

/-- A displayed suffix on every row narrows the complete finite expectation
enclosure, even when the rows have different prefixes and suffixes. -/
theorem extendedPrefixFamilyProbeExpectationBound_refines
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
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound.Refines
      (extendedPrefixFamilyProbeExpectationBound distribution suffix
        extendedRealizes probe factor factorNonnegative sensitive)
      (prefixFamilyProbeExpectationBound distribution probe factor
        factorNonnegative sensitive) := by
  apply distribution.enclosedExpectation_refines
  intro atom member
  exact completedPrefixProbeBound_append_refines atom.item.blocks
    (suffix atom.item) atom.item.witness (extendedRealizes atom.item)
    probe factor factorNonnegative sensitive

/-- Consequently, simultaneous finite suffix extension cannot increase the
weighted rational uncertainty of the prefix family. -/
theorem extendedPrefixFamilyProbeExpectationBound_width_le
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
        factor * CCL.Chordal.chordalSq left right) :
    (extendedPrefixFamilyProbeExpectationBound distribution suffix
      extendedRealizes probe factor factorNonnegative sensitive).width ≤
      (prefixFamilyProbeExpectationBound distribution probe factor
        factorNonnegative sensitive).width :=
  (extendedPrefixFamilyProbeExpectationBound_refines distribution suffix
    extendedRealizes probe factor factorNonnegative sensitive).width_le

/-- A heterogeneous family meets a rational accuracy request exactly when
its displayed finite weighted spread calculation meets that request.  This
allows low-weight rows to remain coarser than high-weight rows. -/
theorem prefixFamilyProbeExpectationBound_width_lt_of_budget
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate)
    (budget : distribution.expectation (fun certificate =>
      2 * (factor * cylinderSpread certificate.blocks)) < target) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width < target := by
  rw [prefixFamilyProbeExpectationBound_width]
  exact budget

/-- Finite completed-block count requested for a positive rational probe
width and positive sensitivity factor. -/
def requiredProbeBlockCount (target factor : Coordinate) : Nat :=
  requiredBlockCount (target / (2 * factor))

/-- Meeting the computed finite block count makes the complete rational
probe enclosure narrower than the requested positive rational width. -/
theorem completedPrefixProbeBound_width_lt_requested
    {blocks : List Block} (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : requiredProbeBlockCount target factor ≤ blocks.length) :
    (completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorPositive.le sensitive).width < target := by
  have scalePositive : (0 : Coordinate) < 2 * factor :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) factorPositive
  have spreadTargetPositive :
      (0 : Coordinate) < target / (2 * factor) :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive scalePositive
  have spreadSmall :
      cylinderSpread blocks < target / (2 * factor) :=
    cylinderSpread_lt_of_requiredBlockCount_le spreadTargetPositive enough
  have scaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      scalePositive spreadSmall
  rw [completedPrefixProbeBound_width]
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

/-- If every displayed prefix row meets the computable half-budget block
count, the entire heterogeneous finite expectation enclosure meets the
original strict rational request. -/
theorem prefixFamilyProbeExpectationBound_width_lt_requested
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 2) factor ≤ atom.item.blocks.length) :
    (prefixFamilyProbeExpectationBound distribution probe factor
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
  unfold prefixFamilyProbeExpectationBound
  apply distribution.enclosedExpectation_width_lt_of_uniform
    (fun certificate => certificate.probeBound probe factor
      factorPositive.le sensitive)
    (target / 2) target
  · intro atom member
    exact (completedPrefixProbeBound_width_lt_requested atom.item.witness
      atom.item.witnessRealizes probe factor factorPositive sensitive
      (target / 2) halfPositive (enough atom member)).le
  · exact halfSmall

end CCL.FiniteMeasure
