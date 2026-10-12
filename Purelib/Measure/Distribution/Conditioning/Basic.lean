module
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Probability
public import Purelib.Measure.Distribution.Density
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Density
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite rational conditioning and partitions

Conditioning is executable reweighting of a displayed finite distribution by
an indicator divided by an explicitly positive rational probability.  Finite
partitions carry direct coverage and disjointness certificates.
-/

namespace Purelib.Measure

namespace Distribution

/-- Every rational Boolean event indicator is nonnegative. -/
private theorem indicator_nonneg {α : Type} (event : α → Bool) (item : α) :
    0 ≤ indicator event item := by
  cases selected : event item <;>
    simp only [indicator, selected] <;> decide

section
open Purelib.Data.Rat
/-- The expectation of an event indicator times a constant is its probability times that constant.

The original finite occurrence list contributes its retained weight exactly when the event selects its payload,
preserving the same constant factor. -/
theorem expectation_indicator_mul_constant {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (constant : Fraction.Rational) :
    distribution.expectation
        (fun item => indicator event item * constant) =
      distribution.probability event * constant := by
  unfold expectation probability
  induction distribution.atoms with
  | nil =>
      simp only [expectationWeight, eventWeight, zero_mul, -eq_self, -iff_self]
      rfl
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · have head : indicator event atom.item = 0 := by
          simp only [indicator, selected, -eq_self, -iff_self]
          rfl
        simp only [expectationWeight, eventWeight, selected, head,
          zero_mul, mul_zero, zero_add, inductionHypothesis, -eq_self, -iff_self]
        rfl
      · have head : indicator event atom.item = 1 := by
          simp only [indicator, selected, -eq_self, -iff_self]
          rfl
        simp only [expectationWeight, eventWeight, selected, head,
          one_mul, inductionHypothesis, -eq_self, -iff_self]
        ring1

/-- Multiply the exact event indicator by the reciprocal of its strictly positive original probability. -/
def conditioningDensity {α : Type} (distribution : Distribution α)
    (condition : α → Bool)
    (_positive : 0 < distribution.probability condition) : α → Fraction.Rational :=
  fun item => indicator condition item *
    (distribution.probability condition)⁻¹

/-- The density of a positive-mass conditioning event is nonnegative at every payload. -/
theorem conditioningDensity_nonnegative {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    ∀ item, 0 ≤ distribution.conditioningDensity condition positive item := by
  intro item
  apply Fraction.Order.Arithmetic.mul_nonneg_direct
  · exact indicator_nonneg condition item
  · exact Fraction.Order.Arithmetic.le_of_lt_direct
      (Fraction.Order.Field.inv_pos_direct positive)

/-- The exact conditioning density has expectation one under the original distribution. -/
theorem conditioningDensity_normalizes {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.expectation
      (distribution.conditioningDensity condition positive) = 1 := by
  change distribution.expectation
    (fun item => indicator condition item *
      (distribution.probability condition)⁻¹) = 1
  rw [distribution.expectation_indicator_mul_constant]
  exact Fraction.Field.mul_inv_cancel
    (distribution.probability condition) positive.ne'

end

/-- Reweight the original distribution by the normalized density of the supplied positive-mass event.

Retain every original occurrence, assigning zero weight outside the event and dividing selected weights by its exact
probability. -/
def conditioned {α : Type} (distribution : Distribution α)
    (condition : α → Bool)
    (positive : 0 < distribution.probability condition) : Distribution α :=
  distribution.reweight
    (distribution.conditioningDensity condition positive)
    (distribution.conditioningDensity_nonnegative condition positive)
    (distribution.conditioningDensity_normalizes condition positive)

/-- Probability in the retained conditioned law equals the original conditional probability ratio.

Both readings use the same original finite distribution and strictly positive conditioning probability, retaining every
selected weight and zeroing the others. -/
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
            Bool.true_and, mul_zero, zero_mul, mul_one, -eq_self, -iff_self] <;> rfl)
    _ = distribution.probability (intersectionEvent event condition) *
          (distribution.probability condition)⁻¹ :=
      distribution.expectation_indicator_mul_constant
        (intersectionEvent event condition)
        (distribution.probability condition)⁻¹
    _ = distribution.conditionalProbability event condition positive := rfl

open Purelib.Data.Rat in
/-- Expectation in the retained conditioned law is original expectation against its exact conditioning density. -/
theorem conditioned_expectation {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition)
    (value : α → Fraction.Rational) :
    (distribution.conditioned condition positive).expectation value =
      distribution.expectation (fun item =>
        distribution.conditioningDensity condition positive item *
          value item) := by
  rw [conditioned, distribution.reweight_expectation]

/-- Conditioning retains the original number of displayed weighted occurrences. -/
theorem conditioned_atoms_length {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).atoms.length =
      distribution.atoms.length := by
  unfold conditioned Distribution.reweight
  exact densityAtoms_length _ _ distribution.atoms

section
open Purelib.Data.Rat
/-- The retained conditioning event has probability one in its conditioned distribution.

Its supplied original positive probability cancels the exact reciprocal factor in the same conditioning density. -/
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
          Bool.true_and, -eq_self, -iff_self] <;> rfl)
  rw [selfIntersection,
    Fraction.Field.div_eq_mul_inv_direct]
  exact Fraction.Field.mul_inv_cancel
    (distribution.probability condition) positive.ne'

/-- The complement of the retained conditioning event has zero probability in its conditioned distribution.

No original payload can satisfy both Boolean conditions, so every retained occurrence contributes zero to their
intersection. -/
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
          Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and, -eq_self, -iff_self] <;> rfl)
  rw [emptyIntersection, distribution.probability_false]
  exact Fraction.Field.zero_div_direct _

/-- Conditioning on the universal event preserves evaluation equivalence with the original distribution.

The original distribution has universal-event probability one, so its exact conditioning density is one at every
retained payload. -/
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
        simp only [intersectionEvent, Bool.and_true, -eq_self, -iff_self]
        rfl)
    rw [sameEvent, distribution.probability_true]
    rw [Fraction.Field.div_eq_mul_inv_direct]
    have inverseOne : (1 : Fraction.Rational)⁻¹ = 1 := by decide
    rw [inverseOne, Fraction.Field.mul_one_direct]
  expectation_eq value := by
    rw [distribution.conditioned_expectation (fun _ => true) positive value]
    exact distribution.expectation_congr _ _ (fun item => by
      unfold conditioningDensity indicator
      rw [distribution.probability_true]
      have inverseOne : (1 : Fraction.Rational)⁻¹ = 1 := by decide
      rw [inverseOne]
      ring1)

/-- Multiplying conditional probability by the positive conditioning probability recovers the original intersection
probability. -/
theorem conditionalProbability_mul_condition {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.conditionalProbability event condition positive *
        distribution.probability condition =
      distribution.probability (intersectionEvent event condition) :=
  Fraction.Field.div_mul_cancel_of_ne
    (distribution.probability (intersectionEvent event condition))
    (distribution.probability condition) positive.ne'

end

/-- Exchanging the two Boolean intersection events preserves their probability.

Each original payload satisfies the same pair of Boolean selections in either order, and the retained weights are
unchanged. -/
theorem probability_intersection_comm {α : Type}
    (distribution : Distribution α) (first second : α → Bool) :
    distribution.probability (intersectionEvent first second) =
      distribution.probability (intersectionEvent second first) := by
  exact distribution.probability_congr _ _ (fun item => by
    cases firstSelected : first item <;>
      cases secondSelected : second item <;>
      simp only [intersectionEvent, firstSelected, secondSelected,
        Bool.false_and, Bool.and_false, Bool.true_and, -eq_self, -iff_self] <;> rfl)

/-- For two positive-probability events, reverse conditional probability using their original marginal probabilities.

Both positivity witnesses concern the same original finite distribution; the identity follows from the exact symmetric
intersection probability. -/
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

end Purelib.Measure

end
