module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Measure.Event.Family
import Purelib.Measure.Distribution.Moments.PaleyZygmund
import Purelib.Measure.Distribution.Occurrence.SecondMoment
public import Purelib.Measure.Distribution.Independence.Basic
public import Purelib.Measure.Event.Occurrence
import Purelib.Measure.Distribution.Occurrence.FirstMoment
import Purelib.Measure.Weighted.Event
import Purelib.Data.List.Event
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Second moments of finite event counts

Expanding the square of a displayed occurrence count gives the exact sum of
the individual probabilities and twice the pair-intersection sum.  Applying
the finite Paley--Zygmund inequality at fraction zero then gives the standard
second-moment lower bound for a finite union.  All sums and events are
displayed and finite.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib in
/-- An event independent of every retained later event factors their intersection-probability sum into its probability
times the original probability sum. -/
private theorem intersectionProbabilitySum_eq_mul_probabilitySum
    {α : Type} (distribution : Measure.Distribution α) (event : α → Bool) :
    ∀ remaining : List (α → Bool),
      (∀ candidate, candidate ∈ remaining →
        distribution.IndependentEvents event candidate) →
      (remaining.map fun candidate => distribution.probability
          (intersectionEvent event candidate)).sum =
        distribution.probability event *
          (remaining.map distribution.probability).sum
  | [], independent => by
      simp only [List.map_nil, List.sum_nil, mul_zero, -eq_self, -iff_self]
      rfl
  | candidate :: remaining, independent => by
      have head := independent candidate List.mem_cons_self
      have tail : ∀ later, later ∈ remaining →
          distribution.IndependentEvents event later :=
        fun later member =>
          independent later (List.mem_cons_of_mem candidate member)
      simp only [List.map_cons, List.sum_cons, -eq_self, -iff_self]
      rw [head,
        distribution.intersectionProbabilitySum_eq_mul_probabilitySum
          event remaining tail]
      ring1

section
open Purelib
open Purelib.Data.Rat
/-- An event indicator has zero covariance with the exact later occurrence count when it is independent of each retained
event. -/
theorem covariance_indicator_occurrenceCount_eq_zero_of_independent
    {α : Type} (distribution : Measure.Distribution α) (event : α → Bool)
    (remaining : List (α → Bool))
    (independent : ∀ candidate, candidate ∈ remaining →
      distribution.IndependentEvents event candidate) :
    distribution.covariance (indicator event) (fun item =>
      (occurrenceCount remaining item : Fraction.Rational)) = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_indicator_mul_occurrenceCount event remaining,
    distribution.expectation_indicator,
    distribution.expectation_occurrenceCount remaining,
    distribution.intersectionProbabilitySum_eq_mul_probabilitySum
      event remaining independent]
  ring1

/-- A pairwise-independent original event list has occurrence-count variance equal to the sum of its Bernoulli
variances. -/
theorem variance_occurrenceCount_of_pairwiseIndependentEventList
    {α : Type} (distribution : Measure.Distribution α)
    (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events) :
    distribution.variance (fun item =>
        (occurrenceCount events item : Fraction.Rational)) =
      (events.map fun event => distribution.probability event *
        (1 - distribution.probability event)).sum := by
  induction events with
  | nil =>
      change distribution.variance (fun _ : α => (0 : Fraction.Rational)) = 0
      exact distribution.variance_constant 0
  | cons event remaining inductionHypothesis =>
      calc
        distribution.variance (fun item =>
              (occurrenceCount (event :: remaining) item : Fraction.Rational)) =
            distribution.variance (fun item =>
              indicator event item +
                (occurrenceCount remaining item : Fraction.Rational)) :=
          distribution.variance_congr _ _
            (cast_occurrenceCount_cons event remaining)
        _ = ((event :: remaining).map fun candidate =>
              distribution.probability candidate *
                (1 - distribution.probability candidate)).sum := by
          rw [distribution.variance_add,
            distribution.variance_indicator,
            distribution.covariance_indicator_occurrenceCount_eq_zero_of_independent
              event remaining independent.1,
            inductionHypothesis independent.2]
          simp only [List.map_cons, List.sum_cons, mul_zero, add_zero, -eq_self, -iff_self]
          rfl

/-- The sum of original Bernoulli event variances is at most the original event-probability sum. -/
private theorem bernoulliVarianceSum_le_probabilitySum
    {α : Type} (distribution : Measure.Distribution α) :
    ∀ events : List (α → Bool),
      (events.map fun event => distribution.probability event *
          (1 - distribution.probability event)).sum ≤
        (events.map distribution.probability).sum
  | [] => le_rfl
  | event :: remaining => by
      let probability := distribution.probability event
      have probabilityNonnegative : 0 ≤ probability :=
        distribution.probability_nonneg event
      have complementFactorLeOne : 1 - probability ≤ 1 := by
        have translated := Fraction.Order.Arithmetic.sub_le_sub_left_direct
          probabilityNonnegative (1 : Fraction.Rational)
        calc
          1 - probability ≤ 1 - 0 := translated
          _ = 1 := by ring1
      have headBound : probability * (1 - probability) ≤ probability := by
        calc
          probability * (1 - probability) ≤ probability * 1 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              complementFactorLeOne probabilityNonnegative
          _ = probability := by ring1
      simpa only [List.map_cons, List.sum_cons] using
        add_le_add headBound
          (distribution.bernoulliVarianceSum_le_probabilitySum remaining)

/-- Pairwise independence bounds the occurrence-count second moment by probability sum plus its square. -/
theorem expectation_occurrenceCount_sq_le_sum_add_sq_of_pairwiseIndependent
    {α : Type} (distribution : Measure.Distribution α)
    (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events) :
    distribution.expectation (fun item =>
        (occurrenceCount events item : Fraction.Rational) ^ 2) ≤
      (events.map distribution.probability).sum +
        (events.map distribution.probability).sum ^ 2 := by
  let count : α → Fraction.Rational := fun item =>
    (occurrenceCount events item : Fraction.Rational)
  let sum := (events.map distribution.probability).sum
  have varianceIdentity := distribution.variance_eq_secondMoment_sub_sq count
  have countMean : distribution.expectation count = sum := by
    exact distribution.expectation_occurrenceCount events
  have varianceFormula :=
    distribution.variance_occurrenceCount_of_pairwiseIndependentEventList
      events independent
  have varianceSumBound :=
    distribution.bernoulliVarianceSum_le_probabilitySum events
  calc
    distribution.expectation (fun item =>
          (occurrenceCount events item : Fraction.Rational) ^ 2) =
        distribution.variance count + sum ^ 2 := by
      rw [varianceIdentity, countMean]
      dsimp only [count]
      ring1
    _ = (events.map fun event => distribution.probability event *
          (1 - distribution.probability event)).sum + sum ^ 2 := by
      rw [varianceFormula]
    _ ≤ sum + sum ^ 2 := add_le_add varianceSumBound le_rfl

end

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- For pairwise-independent events, squared probability sum is bounded by sum plus square times exact union
probability. -/
theorem pairwiseIndependent_union_lower_mul {α : Type}
    (distribution : Measure.Distribution α) (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events) :
    (events.map distribution.probability).sum ^ 2 ≤
      ((events.map distribution.probability).sum +
          (events.map distribution.probability).sum ^ 2) *
        distribution.probability (unionEvents events) := by
  let count : α → Fraction.Rational := fun item =>
    (occurrenceCount events item : Fraction.Rational)
  have countNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ count atom.item := by
    intro atom member
    dsimp only [count]
    simpa only [Nat.cast_zero] using
      Fraction.Cast.Order.natCast_le_direct
        (Nat.zero_le (occurrenceCount events atom.item))
  have multiplicative := distribution.paleyZygmund_mul
    (distribution.aboveFractionOfMeanEvent count 0) count 0 le_rfl
    (by decide) countNonnegative (by
      intro atom atomMember outside
      unfold aboveFractionOfMeanEvent at outside
      have notPositive := decide_eq_false_iff_not.mp outside
      dsimp only [count] at notPositive ⊢
      simpa only [zero_mul] using
        Fraction.Order.Arithmetic.le_of_not_gt_direct notPositive)
  have secondMomentBound :=
    distribution
      |>.expectation_occurrenceCount_sq_le_sum_add_sq_of_pairwiseIndependent
        events independent
  have probabilityNonnegative :=
    distribution.probability_nonneg (unionEvents events)
  have eventProbability :
      distribution.probability
          (distribution.aboveFractionOfMeanEvent count 0) =
        distribution.probability (unionEvents events) :=
    distribution.probability_congr _ _ (fun item => by
      dsimp only [count]
      exact Distribution.aboveFractionZero_occurrenceCount_eq_unionEvents
        distribution events item)
  rw [show distribution.expectation count =
      (events.map distribution.probability).sum by
        exact distribution.expectation_occurrenceCount events,
    show distribution.expectation (fun item => count item ^ 2) =
      distribution.expectation (fun item =>
        (occurrenceCount events item : Fraction.Rational) ^ 2) by rfl,
    eventProbability]
      at multiplicative
  have coefficient : (1 - (0 : Fraction.Rational)) ^ 2 = 1 := by ring1
  rw [coefficient, one_mul] at multiplicative
  exact multiplicative.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      secondMomentBound probabilityNonnegative)

open Purelib in
open Purelib.Data.Rat in
/-- A pairwise-independent event list with positive probability sum has union probability at least that sum divided by
one plus the sum. -/
theorem pairwiseIndependent_union_lower_bound {α : Type}
    (distribution : Measure.Distribution α) (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events)
    (positive : 0 < (events.map distribution.probability).sum) :
    (events.map distribution.probability).sum /
        (1 + (events.map distribution.probability).sum) ≤
      distribution.probability (unionEvents events) := by
  let sum := (events.map distribution.probability).sum
  let unionProbability := distribution.probability (unionEvents events)
  have sumNonnegative : 0 ≤ sum := positive.le
  have denominatorPositive : 0 < 1 + sum :=
    add_pos_of_pos_of_nonneg (by decide) sumNonnegative
  have multiplicative := distribution.pairwiseIndependent_union_lower_mul
    events independent
  have cancelled : sum ≤ unionProbability * (1 + sum) := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := sum)
    · calc
        sum * sum = sum ^ 2 := by ring1
        _ ≤ (sum + sum ^ 2) * unionProbability := multiplicative
        _ = (unionProbability * (1 + sum)) * sum := by ring1
    · exact positive
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  exact cancelled

end Distribution

end Purelib.Measure

end
