import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.AtomOperations
import FiniteMeasure.Valuation
import FiniteMeasure.Sampling
import FiniteMeasure.Normalization
import FiniteMeasure.DistributionEquivalence
import FiniteMeasure.Consolidation
import FiniteMeasure.NormalizedOperations

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace FiniteMeasure

/-- Unit-weight atoms attached to a displayed finite sample list. -/
def unitAtoms {α : Type} : List α → List (Weighted α)
  | [] => []
  | item :: remaining =>
      ⟨item, 1, by decide⟩ :: unitAtoms remaining

theorem unitAtoms_length {α : Type} (samples : List α) :
    (unitAtoms samples).length = samples.length := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [unitAtoms, List.length_cons, inductionHypothesis]

theorem unitAtoms_append {α : Type} (left right : List α) :
    unitAtoms (left ++ right) = unitAtoms left ++ unitAtoms right := by
  induction left with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [List.cons_append, unitAtoms, List.cons_append,
        inductionHypothesis]

theorem totalWeight_unitAtoms {α : Type} (samples : List α) :
    totalWeight (unitAtoms samples) = (samples.length : Coordinate) := by
  induction samples with
  | nil =>
      simp only [unitAtoms, totalWeight, List.length_nil, Nat.cast_zero]
  | cons item remaining inductionHypothesis =>
      simp only [unitAtoms, totalWeight, List.length_cons,
        inductionHypothesis, Nat.cast_succ]
      ring1

/-- Number of displayed samples selected by one executable Boolean event. -/
def countEvent {α : Type} : List α → (α → Bool) → Nat
  | [], _ => 0
  | item :: remaining, event =>
      (if event item then 1 else 0) + countEvent remaining event

/-- Exact multiplicity of one payload in a displayed sample.  Equality is
supplied explicitly, so this is a terminating finite computation. -/
def countItem {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | item :: remaining, target =>
      (if item = target then 1 else 0) + countItem remaining target

/-- A supplied payload is absent from every row of a displayed sample. -/
def SampleAbsent {α : Type} (target : α) : List α → Prop
  | [] => True
  | item :: remaining =>
      item ≠ target ∧ SampleAbsent target remaining

/-- A supplied payload occurs in a displayed sample, expressed by finite
recursion rather than an ambient set. -/
def SampleContains {α : Type} (target : α) : List α → Prop
  | [] => False
  | item :: remaining =>
      item = target ∨ SampleContains target remaining

/-- Recursive sample containment supplies ordinary displayed-list
membership, without requiring equality search. -/
theorem sampleContains_mem {α : Type} (target : α) :
    ∀ {samples : List α}, SampleContains target samples → target ∈ samples
  | [], contains => contains.elim
  | item :: remaining, contains => by
      rcases contains with equal | tailContains
      · exact List.mem_cons.mpr (Or.inl equal.symm)
      · exact List.mem_cons.mpr (Or.inr
          (sampleContains_mem target tailContains))

/-- A row displayed by `unitAtoms` carries a payload occurring in the source
sample list. -/
theorem unitAtoms_member_sampleContains {α : Type}
    (candidate : Weighted α) :
    ∀ {samples : List α}, candidate ∈ unitAtoms samples →
      SampleContains candidate.item samples
  | [], member => (List.not_mem_nil member).elim
  | item :: remaining, member => by
      simp only [unitAtoms, List.mem_cons] at member
      rcases member with equal | tailMember
      · have itemEqual :=
          congrArg (fun row : Weighted α => row.item) equal
        exact Or.inl itemEqual.symm
      · exact Or.inr
          (unitAtoms_member_sampleContains candidate tailMember)

theorem countEvent_atomEvent {α : Type} [DecidableEq α]
    (samples : List α) (target : α) :
    countEvent samples (atomEvent target) = countItem samples target := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      by_cases equal : item = target
      · simp [countEvent, atomEvent, countItem, equal,
          inductionHypothesis]
      · simp [countEvent, atomEvent, countItem, equal,
          inductionHypothesis]

theorem countItem_append {α : Type} [DecidableEq α]
    (left right : List α) (target : α) :
    countItem (left ++ right) target =
      countItem left target + countItem right target := by
  induction left with
  | nil => simp only [List.nil_append, countItem, zero_add]
  | cons item remaining inductionHypothesis =>
      by_cases equal : item = target
      · rw [List.cons_append, countItem, if_pos equal,
          inductionHypothesis, countItem, if_pos equal, Nat.add_assoc]
      · rw [List.cons_append, countItem, if_neg equal,
          inductionHypothesis, countItem, if_neg equal]
        exact (Nat.add_assoc 0 (countItem remaining target)
          (countItem right target)).symm

theorem countItem_le_length {α : Type} [DecidableEq α]
    (samples : List α) (target : α) :
    countItem samples target ≤ samples.length := by
  induction samples with
  | nil => exact le_rfl
  | cons item remaining inductionHypothesis =>
      by_cases equal : item = target
      · simp [countItem, equal]
        omega
      · simp [countItem, equal]
        omega

theorem countItem_eq_zero_of_sampleAbsent
    {α : Type} [DecidableEq α] (target : α) :
    ∀ samples : List α, SampleAbsent target samples →
      countItem samples target = 0
  | [], _ => rfl
  | item :: remaining, absent => by
      rcases absent with ⟨different, remainingAbsent⟩
      simpa [countItem, different] using
        countItem_eq_zero_of_sampleAbsent target remaining remainingAbsent

theorem countItem_pos_of_sampleContains
    {α : Type} [DecidableEq α] (target : α) :
    ∀ samples : List α, SampleContains target samples →
      0 < countItem samples target
  | [], contains => contains.elim
  | item :: remaining, contains => by
      rcases contains with equal | tailContains
      · simp [countItem, equal]
        omega
      · have tailPositive := countItem_pos_of_sampleContains
          target remaining tailContains
        by_cases equal : item = target
        · simp [countItem, equal]
          omega
        · simpa [countItem, equal] using tailPositive

/-- Equality decidability gives a fully constructive finite support split:
the payload is either displayed, or accompanied by a recursive absence
certificate. -/
theorem sampleContains_or_sampleAbsent
    {α : Type} [DecidableEq α] (target : α) :
    ∀ samples : List α,
      SampleContains target samples ∨ SampleAbsent target samples
  | [] => Or.inr trivial
  | item :: remaining => by
      by_cases equal : item = target
      · exact Or.inl (Or.inl equal)
      · rcases sampleContains_or_sampleAbsent target remaining with
          tailContains | tailAbsent
        · exact Or.inl (Or.inr tailContains)
        · exact Or.inr ⟨equal, tailAbsent⟩

theorem sampleContains_not_sampleAbsent
    {α : Type} (target : α) :
    ∀ samples : List α,
      SampleContains target samples → ¬SampleAbsent target samples
  | [], contains => contains.elim
  | item :: remaining, contains => by
      intro absent
      rcases contains with equal | tailContains
      · exact absent.1 equal
      · exact sampleContains_not_sampleAbsent target remaining
          tailContains absent.2

theorem eventWeight_unitAtoms {α : Type} (samples : List α)
    (event : α → Bool) :
    eventWeight (unitAtoms samples) event =
      (countEvent samples event : Coordinate) := by
  induction samples with
  | nil =>
      simp only [unitAtoms, eventWeight, countEvent, Nat.cast_zero]
  | cons item remaining inductionHypothesis =>
      cases selected : event item <;>
        simp only [unitAtoms, eventWeight, countEvent, selected,
          Bool.false_eq_true, ↓reduceIte, inductionHypothesis,
          Nat.cast_add, Nat.cast_one, zero_add]

theorem countEvent_map {α β : Type} (samples : List α)
    (function : α → β) (event : β → Bool) :
    countEvent (samples.map function) event =
      countEvent samples (fun item => event (function item)) := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [List.map_cons, countEvent, inductionHypothesis]

/-- Rational sum of an observable over a displayed sample list. -/
def sumValues {α : Type} : List α → (α → Coordinate) → Coordinate
  | [], _ => 0
  | item :: remaining, value =>
      value item + sumValues remaining value

/-- Pointwise equality preserves the explicitly accumulated sample sum. -/
theorem sumValues_congr {α : Type} (samples : List α)
    (left right : α → Coordinate)
    (equal : ∀ item, left item = right item) :
    sumValues samples left = sumValues samples right := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      rw [sumValues, sumValues, equal item, inductionHypothesis]

theorem sumValues_eq_sampleSum {α : Type}
    (samples : List α) (value : α → Coordinate) :
    sumValues samples value = sampleSum value samples := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [sumValues, sampleSum, inductionHypothesis]

theorem sumValues_map {α β : Type} (samples : List α)
    (function : α → β) (value : β → Coordinate) :
    sumValues (samples.map function) value =
      sumValues samples (fun item => value (function item)) := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [List.map_cons, sumValues, inductionHypothesis]

theorem expectationWeight_unitAtoms {α : Type} (samples : List α)
    (value : α → Coordinate) :
    Distribution.expectationWeight (unitAtoms samples) value =
      sumValues samples value := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [unitAtoms, Distribution.expectationWeight,
        sumValues, inductionHypothesis, one_mul]

/-- Exact nonnormalized counting content of a displayed sample list. -/
def countingContent {α : Type} (samples : List α) : FiniteContent α :=
  ⟨unitAtoms samples⟩

theorem countingContent_append {α : Type} (left right : List α) :
    countingContent (left ++ right) =
      (countingContent left).append (countingContent right) := by
  unfold countingContent FiniteContent.append
  congr 1
  exact unitAtoms_append left right

theorem countingContent_total {α : Type} (samples : List α) :
    (countingContent samples).total = (samples.length : Coordinate) :=
  totalWeight_unitAtoms samples

theorem countingContent_measure {α : Type} (samples : List α)
    (event : α → Bool) :
    (countingContent samples).measure event =
      (countEvent samples event : Coordinate) :=
  eventWeight_unitAtoms samples event

theorem countingContent_integral {α : Type} (samples : List α)
    (value : α → Coordinate) :
    (countingContent samples).integral value = sumValues samples value :=
  expectationWeight_unitAtoms samples value

/-- Uniform empirical distribution on a displayed nonempty sample list. -/
def empiricalDistribution {α : Type} (samples : List α)
    (positiveLength : 0 < samples.length) : Distribution α where
  atoms := scaleAtoms
    (1 / (samples.length : Coordinate))
    (RFAP.ConstructiveFraction.div_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.natCast_pos_direct positiveLength).le)
    (unitAtoms samples)
  total_one := by
    rw [totalWeight_scaleAtoms, totalWeight_unitAtoms]
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1
      (samples.length : Coordinate)
      (RFAP.ConstructiveFraction.natCast_pos_direct positiveLength).ne'

/-- Every atom payload of an empirical distribution occurs in its displayed
sample list. -/
theorem empiricalDistribution_atom_sampleContains {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (candidate : Weighted α)
    (member : candidate ∈
      (empiricalDistribution samples positiveLength).atoms) :
    SampleContains candidate.item samples := by
  unfold empiricalDistribution at member
  rcases mem_scaleAtoms_source _ _ candidate member with
      ⟨source, sourceMember, itemEqual⟩
  simpa only [itemEqual] using
    unitAtoms_member_sampleContains source sourceMember

theorem empiricalDistribution_atoms_length {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length) :
    (empiricalDistribution samples positiveLength).atoms.length =
      samples.length := by
  simp only [empiricalDistribution, scaleAtoms_length, unitAtoms_length]

/-- Empirical probability is the exact selected count divided by sample
size. -/
theorem empiricalDistribution_probability {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (event : α → Bool) :
    (empiricalDistribution samples positiveLength).probability event =
      (countEvent samples event : Coordinate) /
        (samples.length : Coordinate) := by
  unfold Distribution.probability empiricalDistribution
  rw [eventWeight_scaleAtoms, eventWeight_unitAtoms]
  change (1 * (samples.length : Coordinate)⁻¹) *
      (countEvent samples event : Coordinate) =
    (countEvent samples event : Coordinate) *
      (samples.length : Coordinate)⁻¹
  rw [RFAP.ConstructiveFraction.one_mul]
  exact RFAP.ConstructiveFraction.mul_comm _ _

/-- Empirical mass at one decidable payload is its exact displayed frequency
divided by the finite sample size. -/
theorem empiricalDistribution_atomMass {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalDistribution samples positiveLength).atomMass item =
      (countEvent samples (atomEvent item) : Coordinate) /
        (samples.length : Coordinate) :=
  empiricalDistribution_probability samples positiveLength (atomEvent item)

/-- The atom mass is literally the rational multiplicity of the payload in
the displayed sample, divided by the displayed sample size. -/
theorem empiricalDistribution_atomMass_eq_countItem
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalDistribution samples positiveLength).atomMass item =
      (countItem samples item : Coordinate) /
        (samples.length : Coordinate) := by
  rw [empiricalDistribution_atomMass, countEvent_atomEvent]

theorem empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α)
    (absent : SampleAbsent item samples) :
    (empiricalDistribution samples positiveLength).atomMass item = 0 := by
  rw [empiricalDistribution_atomMass_eq_countItem,
    countItem_eq_zero_of_sampleAbsent item samples absent, Nat.cast_zero]
  exact RFAP.ConstructiveFraction.zero_div_direct _

/-- Every actually displayed payload has strictly positive rational
empirical mass. -/
theorem empiricalDistribution_atomMass_pos_of_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α)
    (contains : SampleContains item samples) :
    0 < (empiricalDistribution samples positiveLength).atomMass item := by
  rw [empiricalDistribution_atomMass_eq_countItem]
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (countItem_pos_of_sampleContains item samples contains))
    (RFAP.ConstructiveFraction.natCast_pos_direct positiveLength)

theorem empiricalDistribution_atomMass_eq_zero_iff_sampleAbsent
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalDistribution samples positiveLength).atomMass item = 0 ↔
      SampleAbsent item samples := by
  constructor
  · intro massZero
    rcases sampleContains_or_sampleAbsent item samples with
        contains | absent
    · have positive :=
        empiricalDistribution_atomMass_pos_of_sampleContains
          samples positiveLength item contains
      rw [massZero] at positive
      exact (positive.2 le_rfl).elim
    · exact absent
  · exact empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
      samples positiveLength item

theorem empiricalDistribution_atomMass_pos_iff_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    0 < (empiricalDistribution samples positiveLength).atomMass item ↔
      SampleContains item samples := by
  constructor
  · intro positive
    rcases sampleContains_or_sampleAbsent item samples with
        contains | absent
    · exact contains
    · have massZero :=
        empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
          samples positiveLength item absent
      rw [massZero] at positive
      exact (positive.2 le_rfl).elim
  · exact empiricalDistribution_atomMass_pos_of_sampleContains
      samples positiveLength item

/-- Empirical expectation is the exact rational sample sum divided by sample
size. -/
theorem empiricalDistribution_expectation {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    (empiricalDistribution samples positiveLength).expectation value =
      sumValues samples value / (samples.length : Coordinate) := by
  unfold Distribution.expectation empiricalDistribution
  rw [expectationWeight_scaleAtoms, expectationWeight_unitAtoms]
  change (1 * (samples.length : Coordinate)⁻¹) * sumValues samples value =
    sumValues samples value * (samples.length : Coordinate)⁻¹
  rw [RFAP.ConstructiveFraction.one_mul]
  exact RFAP.ConstructiveFraction.mul_comm _ _

/-- Empirical expectation is literally the exact finite sample-mean
operation used by the repeated-sampling layer. -/
theorem empiricalDistribution_expectation_eq_sampleMean {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    (empiricalDistribution samples positiveLength).expectation value =
      Distribution.sampleMean samples.length value samples := by
  rw [empiricalDistribution_expectation,
    sumValues_eq_sampleSum]
  unfold Distribution.sampleMean
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.mul_comm]

/-- The empirical probability of an event is exactly the event-frequency
operation used by the finite iid sampling layer. -/
theorem empiricalDistribution_probability_eq_eventFrequency {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (event : α → Bool) :
    (empiricalDistribution samples positiveLength).probability event =
      Distribution.eventFrequency samples.length event samples := by
  rw [← (empiricalDistribution samples positiveLength).expectation_indicator]
  unfold Distribution.eventFrequency
  exact empiricalDistribution_expectation_eq_sampleMean samples
    positiveLength (Distribution.indicator event)

/-- Empirical variance is itself an empirical mean: the exact rational
average of the displayed squared deviations. -/
theorem empiricalDistribution_variance_eq_sampleMean {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    (empiricalDistribution samples positiveLength).variance value =
      Distribution.sampleMean samples.length
        (fun item =>
          (value item -
            (empiricalDistribution samples positiveLength).expectation value) ^ 2)
        samples := by
  unfold Distribution.variance Distribution.varianceAround
  exact empiricalDistribution_expectation_eq_sampleMean samples positiveLength _

/-- Executable empirical histogram: equal payloads are merged by finite
recursion, with no quotient or chosen representative. -/
def empiricalHistogram {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    Distribution α :=
  (empiricalDistribution samples positiveLength).consolidate

theorem empiricalHistogram_evaluationEquivalent
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    Distribution.EvaluationEquivalent
      (empiricalHistogram samples positiveLength)
      (empiricalDistribution samples positiveLength) :=
  (empiricalDistribution samples positiveLength).consolidate_evaluationEquivalent

theorem empiricalHistogram_atoms_length_le
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    (empiricalHistogram samples positiveLength).atoms.length ≤
      samples.length := by
  calc
    (empiricalHistogram samples positiveLength).atoms.length ≤
        (empiricalDistribution samples positiveLength).atoms.length :=
      (empiricalDistribution samples positiveLength).consolidate_atoms_length_le
    _ = samples.length :=
      empiricalDistribution_atoms_length samples positiveLength

theorem empiricalHistogram_noRepeatedPayloads
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) :
    NoRepeatedPayloads (empiricalHistogram samples positiveLength).atoms :=
  (empiricalDistribution samples positiveLength).consolidate_noRepeatedPayloads

theorem empiricalHistogram_atomMass_eq_countItem
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    (empiricalHistogram samples positiveLength).atomMass item =
      (countItem samples item : Coordinate) /
        (samples.length : Coordinate) := by
  rw [empiricalHistogram,
    Distribution.consolidate_atomMass,
    empiricalDistribution_atomMass_eq_countItem]

theorem empiricalHistogram_atomMass_pos_of_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α)
    (contains : SampleContains item samples) :
    0 < (empiricalHistogram samples positiveLength).atomMass item := by
  rw [empiricalHistogram_atomMass_eq_countItem]
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (countItem_pos_of_sampleContains item samples contains))
    (RFAP.ConstructiveFraction.natCast_pos_direct positiveLength)

theorem empiricalHistogram_atomMass_pos_iff_sampleContains
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length) (item : α) :
    0 < (empiricalHistogram samples positiveLength).atomMass item ↔
      SampleContains item samples := by
  rw [empiricalHistogram,
    Distribution.consolidate_atomMass,
    empiricalDistribution_atomMass_pos_iff_sampleContains]

/-- Direct empirical normalization and normalization of the unit-weight
counting content agree on every executable event and rational observable. -/
theorem empiricalDistribution_evaluationEquivalent_normalizedCounting
    {α : Type} (samples : List α) (positiveLength : 0 < samples.length)
    (positiveTotal : 0 < (countingContent samples).total) :
    Distribution.EvaluationEquivalent
      (empiricalDistribution samples positiveLength)
      ((countingContent samples).normalize positiveTotal) where
  probability_eq event := by
    rw [empiricalDistribution_probability,
      FiniteContent.normalize_probability,
      countingContent_measure, countingContent_total]
  expectation_eq value := by
    rw [empiricalDistribution_expectation,
      FiniteContent.normalize_expectation,
      countingContent_integral, countingContent_total]

/-- Empirical formation commutes observationally with an explicit finite
pushforward of the displayed sample list. -/
theorem empiricalDistribution_map_evaluationEquivalent
    {α β : Type} (samples : List α) (positiveLength : 0 < samples.length)
    (function : α → β) :
    Distribution.EvaluationEquivalent
      ((empiricalDistribution samples positiveLength).map function)
      (empiricalDistribution (samples.map function) (by
        simpa only [List.length_map] using positiveLength)) where
  probability_eq event := by
    rw [Distribution.map_probability,
      empiricalDistribution_probability,
      empiricalDistribution_probability,
      countEvent_map]
    simp only [List.length_map]
  expectation_eq value := by
    rw [Distribution.map_expectation,
      empiricalDistribution_expectation,
      empiricalDistribution_expectation,
      sumValues_map]
    simp only [List.length_map]

/-- Pooling two displayed nonempty sample lists gives the rational mixture
of their empirical laws, with exact coefficients determined by the two
finite counting contents. -/
theorem empiricalDistribution_append_evaluationEquivalent
    {α : Type} (left right : List α)
    (leftPositive : 0 < left.length) (rightPositive : 0 < right.length) :
    Distribution.EvaluationEquivalent
      (empiricalDistribution (left ++ right) (by
        simp only [List.length_append]
        omega))
      ((empiricalDistribution left leftPositive).mixture
        (empiricalDistribution right rightPositive)
        (FiniteContent.appendMixingWeight
          (countingContent left) (countingContent right) (by
            rw [countingContent_total, countingContent_total]
            simpa only [zero_add] using
              RFAP.ConstructiveFraction.add_lt_add_direct
                (RFAP.ConstructiveFraction.natCast_pos_direct leftPositive)
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  rightPositive)))) := by
  have leftTotalPositive : 0 < (countingContent left).total := by
    rw [countingContent_total]
    exact RFAP.ConstructiveFraction.natCast_pos_direct leftPositive
  have rightTotalPositive : 0 < (countingContent right).total := by
    rw [countingContent_total]
    exact RFAP.ConstructiveFraction.natCast_pos_direct rightPositive
  have sumTotalPositive :
      0 < (countingContent left).total + (countingContent right).total := by
    simpa only [zero_add] using
      RFAP.ConstructiveFraction.add_lt_add_direct
        leftTotalPositive rightTotalPositive
  have appendLengthPositive : 0 < (left ++ right).length := by
    simp only [List.length_append]
    omega
  have appendTotalPositive :
      0 < (countingContent (left ++ right)).total := by
    rw [countingContent_total]
    exact RFAP.ConstructiveFraction.natCast_pos_direct appendLengthPositive
  have empiricalToCountingRaw :=
    empiricalDistribution_evaluationEquivalent_normalizedCounting
      (left ++ right) appendLengthPositive appendTotalPositive
  have empiricalToCounting :
      Distribution.EvaluationEquivalent
        (empiricalDistribution (left ++ right) appendLengthPositive)
        (((countingContent left).append (countingContent right)).normalize
          (by
            rw [FiniteContent.append_total]
            exact sumTotalPositive)) := by
    simpa only [countingContent_append] using empiricalToCountingRaw
  have appendToMixture :=
    FiniteContent.append_normalize_evaluationEquivalent
      (countingContent left) (countingContent right)
      leftTotalPositive rightTotalPositive
  have components :=
    (empiricalDistribution_evaluationEquivalent_normalizedCounting
      left leftPositive leftTotalPositive).symm.mixture
      (empiricalDistribution_evaluationEquivalent_normalizedCounting
        right rightPositive rightTotalPositive).symm
      (FiniteContent.appendMixingWeight
        (countingContent left) (countingContent right)
        sumTotalPositive)
  exact (empiricalToCounting.trans appendToMixture).trans components

/-- Canonical rational sample-size coefficient for pooling two displayed
nonempty empirical samples. -/
def empiricalAppendWeight {α : Type} (left right : List α)
    (leftPositive : 0 < left.length) (rightPositive : 0 < right.length) :
    MixingWeight :=
  FiniteContent.appendMixingWeight
    (countingContent left) (countingContent right) (by
      rw [countingContent_total, countingContent_total]
      simpa only [zero_add] using
        RFAP.ConstructiveFraction.add_lt_add_direct
          (RFAP.ConstructiveFraction.natCast_pos_direct leftPositive)
          (RFAP.ConstructiveFraction.natCast_pos_direct rightPositive))

theorem empiricalAppendWeight_coefficient {α : Type}
    (left right : List α) (leftPositive : 0 < left.length)
    (rightPositive : 0 < right.length) :
    (empiricalAppendWeight left right leftPositive rightPositive).coefficient =
      (left.length : Coordinate) /
        ((left.length : Coordinate) + (right.length : Coordinate)) := by
  unfold empiricalAppendWeight FiniteContent.appendMixingWeight
  change (countingContent left).total /
      ((countingContent left).total + (countingContent right).total) = _
  rw [countingContent_total, countingContent_total]

theorem empiricalDistribution_append_mixture {α : Type}
    (left right : List α) (leftPositive : 0 < left.length)
    (rightPositive : 0 < right.length) :
    Distribution.EvaluationEquivalent
      (empiricalDistribution (left ++ right) (by
        simp only [List.length_append]
        omega))
      ((empiricalDistribution left leftPositive).mixture
        (empiricalDistribution right rightPositive)
        (empiricalAppendWeight left right leftPositive rightPositive)) := by
  unfold empiricalAppendWeight
  exact empiricalDistribution_append_evaluationEquivalent
    left right leftPositive rightPositive

/-- Exact pooled-sample variance decomposition into within-sample and
between-sample rational terms. -/
theorem empiricalDistribution_append_variance {α : Type}
    (left right : List α) (leftPositive : 0 < left.length)
    (rightPositive : 0 < right.length) (value : α → Coordinate) :
    (empiricalDistribution (left ++ right) (by
        simp only [List.length_append]
        omega)).variance value =
      let weight := empiricalAppendWeight
        left right leftPositive rightPositive
      weight.coefficient *
          (empiricalDistribution left leftPositive).variance value +
        weight.complement *
          (empiricalDistribution right rightPositive).variance value +
        weight.coefficient * weight.complement *
          ((empiricalDistribution left leftPositive).expectation value -
            (empiricalDistribution right rightPositive).expectation value) ^ 2 := by
  let weight := empiricalAppendWeight left right leftPositive rightPositive
  have equivalent := empiricalDistribution_append_mixture
    left right leftPositive rightPositive
  calc
    (empiricalDistribution (left ++ right) (by
        simp only [List.length_append]
        omega)).variance value =
        ((empiricalDistribution left leftPositive).mixture
          (empiricalDistribution right rightPositive) weight).variance value :=
      equivalent.variance_eq value
    _ = weight.coefficient *
          (empiricalDistribution left leftPositive).variance value +
        weight.complement *
          (empiricalDistribution right rightPositive).variance value +
        weight.coefficient * weight.complement *
          ((empiricalDistribution left leftPositive).expectation value -
            (empiricalDistribution right rightPositive).expectation value) ^ 2 :=
      (empiricalDistribution left leftPositive).mixture_variance
        (empiricalDistribution right rightPositive) weight value

end FiniteMeasure
