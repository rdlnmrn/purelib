import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Density
import FiniteMeasure.Family
import FiniteMeasure.ZeroWeight
import FiniteMeasure.DistributionEquivalence

/-!
# Finite rational conditioning and partitions

Conditioning is executable reweighting of a displayed finite distribution by
an indicator divided by an explicitly positive rational probability.  Finite
partitions carry direct coverage and disjointness certificates.
-/

namespace FiniteMeasure

namespace Distribution

private theorem indicator_nonneg {α : Type} (event : α → Bool) (item : α) :
    0 ≤ indicator event item := by
  cases selected : event item <;>
    simp only [indicator, selected] <;> decide

theorem expectation_indicator_mul_constant {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (constant : Coordinate) :
    distribution.expectation
        (fun item => indicator event item * constant) =
      distribution.probability event * constant := by
  unfold expectation probability
  induction distribution.atoms with
  | nil =>
      simp only [expectationWeight, eventWeight, zero_mul]
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · have head : indicator event atom.item = 0 := by
          simp only [indicator, selected]
        simp only [expectationWeight, eventWeight, selected, head,
          zero_mul, mul_zero, zero_add, inductionHypothesis]
      · have head : indicator event atom.item = 1 := by
          simp only [indicator, selected]
        simp only [expectationWeight, eventWeight, selected, head,
          one_mul, inductionHypothesis]
        ring1

/-- Explicit rational density used to condition on a positive-probability
finite event. -/
def conditioningDensity {α : Type} (distribution : Distribution α)
    (condition : α → Bool)
    (_positive : 0 < distribution.probability condition) : α → Coordinate :=
  fun item => indicator condition item *
    (distribution.probability condition)⁻¹

theorem conditioningDensity_nonnegative {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    ∀ item, 0 ≤ distribution.conditioningDensity condition positive item := by
  intro item
  apply RFAP.ConstructiveFraction.mul_nonneg_direct
  · exact indicator_nonneg condition item
  · exact RFAP.ConstructiveFraction.le_of_lt_direct
      (RFAP.ConstructiveFraction.inv_pos_direct positive)

theorem conditioningDensity_normalizes {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.expectation
      (distribution.conditioningDensity condition positive) = 1 := by
  change distribution.expectation
    (fun item => indicator condition item *
      (distribution.probability condition)⁻¹) = 1
  rw [distribution.expectation_indicator_mul_constant]
  exact RFAP.ConstructiveFraction.mul_inv_cancel
    (distribution.probability condition) positive.ne'

/-- The displayed finite distribution conditioned on an explicitly positive
Boolean event. -/
def conditioned {α : Type} (distribution : Distribution α)
    (condition : α → Bool)
    (positive : 0 < distribution.probability condition) : Distribution α :=
  distribution.reweight
    (distribution.conditioningDensity condition positive)
    (distribution.conditioningDensity_nonnegative condition positive)
    (distribution.conditioningDensity_normalizes condition positive)

theorem conditioned_probability {α : Type}
    (distribution : Distribution α) (condition event : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).probability event =
      distribution.conditionalProbability event condition positive := by
  rw [conditioned, distribution.reweight_probability]
  calc
    distribution.expectation (fun item =>
        distribution.conditioningDensity condition positive item *
          indicator event item) =
        distribution.expectation (fun item =>
          indicator (intersectionEvent event condition) item *
            (distribution.probability condition)⁻¹) :=
      distribution.expectation_congr _ _ (fun item => by
        cases conditionSelected : condition item <;>
          cases eventSelected : event item <;>
          simp only [conditioningDensity, indicator, conditionSelected,
            eventSelected, intersectionEvent, Bool.false_and, Bool.and_false,
            Bool.true_and, mul_zero, zero_mul, mul_one])
    _ = distribution.probability (intersectionEvent event condition) *
          (distribution.probability condition)⁻¹ :=
      distribution.expectation_indicator_mul_constant
        (intersectionEvent event condition)
        (distribution.probability condition)⁻¹
    _ = distribution.conditionalProbability event condition positive := rfl

theorem conditioned_expectation {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition)
    (value : α → Coordinate) :
    (distribution.conditioned condition positive).expectation value =
      distribution.expectation (fun item =>
        distribution.conditioningDensity condition positive item *
          value item) := by
  rw [conditioned, distribution.reweight_expectation]

theorem conditioned_atoms_length {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).atoms.length =
      distribution.atoms.length := by
  unfold conditioned Distribution.reweight
  exact densityAtoms_length _ _ distribution.atoms

/-- The explicitly positive conditioning event has probability one after
finite conditioning. -/
theorem conditioned_probability_condition {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).probability condition =
      1 := by
  rw [distribution.conditioned_probability condition condition positive]
  unfold conditionalProbability
  have selfIntersection := distribution.probability_congr
    (intersectionEvent condition condition) condition (fun item => by
      cases selected : condition item <;>
        simp only [intersectionEvent, selected, Bool.false_and,
          Bool.true_and])
  rw [selfIntersection,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  exact RFAP.ConstructiveFraction.mul_inv_cancel
    (distribution.probability condition) positive.ne'

/-- The executable complement of the conditioning event has exactly zero
probability after finite conditioning. -/
theorem conditioned_probability_complement {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).probability
        (complementEvent condition) = 0 := by
  rw [distribution.conditioned_probability
    condition (complementEvent condition) positive]
  unfold conditionalProbability
  have emptyIntersection := distribution.probability_congr
    (intersectionEvent (complementEvent condition) condition)
    (fun _ => false) (fun item => by
      cases selected : condition item <;>
        simp only [intersectionEvent, complementEvent, selected,
          Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and])
  rw [emptyIntersection, distribution.probability_false]
  exact RFAP.ConstructiveFraction.zero_div_direct _

/-- Conditioning on the always-true executable event preserves all exact
finite evaluations. -/
theorem conditioned_true_evaluationEquivalent {α : Type}
    (distribution : Distribution α)
    (positive : 0 < distribution.probability (fun _ => true)) :
    EvaluationEquivalent
      (distribution.conditioned (fun _ => true) positive) distribution where
  probability_eq event := by
    rw [distribution.conditioned_probability (fun _ => true) event positive]
    unfold conditionalProbability
    have sameEvent := distribution.probability_congr
      (intersectionEvent event (fun _ => true)) event (fun item => by
        simp only [intersectionEvent, Bool.and_true])
    rw [sameEvent, distribution.probability_true]
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    have inverseOne : (1 : Coordinate)⁻¹ = 1 := by decide
    rw [inverseOne, RFAP.ConstructiveFraction.mul_one_direct]
  expectation_eq value := by
    rw [distribution.conditioned_expectation (fun _ => true) positive value]
    exact distribution.expectation_congr _ _ (fun item => by
      unfold conditioningDensity indicator
      rw [distribution.probability_true]
      have inverseOne : (1 : Coordinate)⁻¹ = 1 := by decide
      rw [inverseOne]
      ring1)

theorem conditionalProbability_mul_condition {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.conditionalProbability event condition positive *
        distribution.probability condition =
      distribution.probability (intersectionEvent event condition) :=
  RFAP.ConstructiveFraction.div_mul_cancel_of_ne
    (distribution.probability (intersectionEvent event condition))
    (distribution.probability condition) positive.ne'

theorem probability_intersection_comm {α : Type}
    (distribution : Distribution α) (first second : α → Bool) :
    distribution.probability (intersectionEvent first second) =
      distribution.probability (intersectionEvent second first) := by
  exact distribution.probability_congr _ _ (fun item => by
    cases firstSelected : first item <;>
      cases secondSelected : second item <;>
      simp only [intersectionEvent, firstSelected, secondSelected,
        Bool.false_and, Bool.and_false, Bool.true_and])

/-- Exact finite Bayes identity, with positivity supplied for both displayed
conditioning events. -/
theorem bayes {α : Type} (distribution : Distribution α)
    (first second : α → Bool)
    (firstPositive : 0 < distribution.probability first)
    (secondPositive : 0 < distribution.probability second) :
    distribution.conditionalProbability first second secondPositive =
      distribution.conditionalProbability second first firstPositive *
        distribution.probability first /
          distribution.probability second := by
  calc
    distribution.conditionalProbability first second secondPositive =
        distribution.probability (intersectionEvent first second) /
          distribution.probability second := rfl
    _ = distribution.probability (intersectionEvent second first) /
          distribution.probability second := by
      rw [distribution.probability_intersection_comm first second]
    _ = (distribution.conditionalProbability second first firstPositive *
            distribution.probability first) /
          distribution.probability second := by
      rw [distribution.conditionalProbability_mul_condition second first
        firstPositive]
    _ = distribution.conditionalProbability second first firstPositive *
          distribution.probability first /
            distribution.probability second := rfl

end Distribution

/-- A displayed finite family of Boolean events that is disjoint and covers
every displayed atom of the distribution. -/
structure EventPartition {α : Type} (distribution : Distribution α) where
  events : List (α → Bool)
  disjoint : MutuallyDisjointOn distribution.atoms events
  covers : ∀ atom, atom ∈ distribution.atoms →
    unionEvents events atom.item = true

namespace EventPartition

/-- Intersect every member of a displayed finite event family with one
additional executable event. -/
def intersectEvents {α : Type} (event : α → Bool) :
    List (α → Bool) → List (α → Bool)
  | [] => []
  | member :: remaining =>
      intersectionEvent event member :: intersectEvents event remaining

theorem unionEvents_intersectEvents {α : Type}
    (event : α → Bool) : ∀ (events : List (α → Bool)) (item : α),
    unionEvents (intersectEvents event events) item =
      intersectionEvent event (unionEvents events) item
  | [], item => by
      simp only [intersectEvents, unionEvents, intersectionEvent,
        Bool.and_false]
  | member :: remaining, item => by
      cases eventSelected : event item <;>
        cases memberSelected : member item <;>
        simp only [intersectEvents, unionEvents, unionEvent,
          intersectionEvent,
          unionEvents_intersectEvents event remaining item, eventSelected,
          memberSelected, Bool.false_and, Bool.true_and,
          Bool.false_or, Bool.true_or]

theorem mutuallyDisjointOn_intersectEvents {α : Type}
    (atoms : List (Weighted α)) (event : α → Bool) :
    ∀ {events : List (α → Bool)},
      MutuallyDisjointOn atoms events →
        MutuallyDisjointOn atoms (intersectEvents event events)
  | [], disjoint => trivial
  | member :: remaining, disjoint => by
      constructor
      · intro atom atomMember selected
        apply disjoint.1 atom atomMember
        have memberSelected : member atom.item = true :=
          (Bool.and_eq_true_iff.mp selected.1).2
        have remainingSelected : unionEvents remaining atom.item = true := by
          have mappedSelected := selected.2
          rw [unionEvents_intersectEvents event remaining atom.item]
            at mappedSelected
          exact (Bool.and_eq_true_iff.mp mappedSelected).2
        exact ⟨memberSelected, remainingSelected⟩
      · exact mutuallyDisjointOn_intersectEvents atoms event disjoint.2

theorem probability_union {α : Type} {distribution : Distribution α}
    (partition : EventPartition distribution) :
    distribution.probability (unionEvents partition.events) = 1 := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · exact distribution.probability_le_one _
  · rw [← distribution.probability_true]
    apply eventWeight_mono
    intro atom member selected
    exact partition.covers atom member

/-- Exact normalization of the probability vector of a displayed finite
partition. -/
theorem probabilities_sum_one {α : Type}
    {distribution : Distribution α}
    (partition : EventPartition distribution) :
    (partition.events.map distribution.probability).sum = 1 := by
  rw [← distribution.probability_unionEvents_of_disjoint partition.disjoint]
  exact partition.probability_union

/-- Exact finite law of total probability over a displayed partition,
written as a sum of the joint event pieces. -/
theorem total_probability {α : Type}
    {distribution : Distribution α}
    (partition : EventPartition distribution) (event : α → Bool) :
    ((intersectEvents event partition.events).map
      distribution.probability).sum = distribution.probability event := by
  rw [← distribution.probability_unionEvents_of_disjoint
    (mutuallyDisjointOn_intersectEvents distribution.atoms event
      partition.disjoint)]
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  rw [unionEvents_intersectEvents]
  unfold intersectionEvent
  rw [partition.covers atom member]
  cases selected : event atom.item <;> rfl

end EventPartition

end FiniteMeasure
