import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.OccurrenceCount
import FiniteMeasure.Independence
import FiniteMeasure.OneSidedMoments

/-!
# Second moments of finite event counts

Expanding the square of a displayed occurrence count gives the exact sum of
the individual probabilities and twice the pair-intersection sum.  Applying
the finite Paley--Zygmund inequality at fraction zero then gives the standard
second-moment lower bound for a finite union.  All sums and events are
displayed and finite.
-/

namespace FiniteMeasure

/-- Number of unordered pairs of positions whose two events both occur. -/
def pairOccurrenceCount {α : Type} : List (α → Bool) → α → Nat
  | [], _ => 0
  | event :: remaining, item =>
      (if event item then occurrenceCount remaining item else 0) +
        pairOccurrenceCount remaining item

/-- Casting the pair count exposes the pairs formed by a selected head and
the recursively counted pairs in the tail. -/
theorem cast_pairOccurrenceCount_cons {α : Type}
    (event : α → Bool) (remaining : List (α → Bool)) (item : α) :
    (pairOccurrenceCount (event :: remaining) item : Coordinate) =
      Distribution.indicator event item *
          (occurrenceCount remaining item : Coordinate) +
        (pairOccurrenceCount remaining item : Coordinate) := by
  cases selected : event item <;>
    simp only [pairOccurrenceCount, selected, Bool.false_eq_true,
      ↓reduceIte, Distribution.indicator, zero_mul, zero_add, one_mul,
      Nat.cast_add]

/-- Pointwise second Bonferroni combinatorics: occurrences minus occurring
pairs never exceed the indicator that at least one event occurs. -/
theorem occurrenceCount_sub_pairOccurrenceCount_le_indicator_union
    {α : Type} : ∀ (events : List (α → Bool)) (item : α),
    (occurrenceCount events item : Coordinate) -
        (pairOccurrenceCount events item : Coordinate) ≤
      Distribution.indicator (unionEvents events) item
  | [], item => by
      change (0 : Coordinate) - 0 ≤ 0
      rw [sub_self]
  | event :: remaining, item => by
      cases selected : event item
      · simpa only [occurrenceCount, pairOccurrenceCount, selected,
          Bool.false_eq_true, ↓reduceIte, Nat.zero_add, unionEvents,
          unionEvent, Bool.false_or, Distribution.indicator] using
          occurrenceCount_sub_pairOccurrenceCount_le_indicator_union
            remaining item
      · have pairNonnegative :
            0 ≤ (pairOccurrenceCount remaining item : Coordinate) := by
          simpa only [Nat.cast_zero] using
            RFAP.ConstructiveFraction.natCast_le_direct
              (Nat.zero_le (pairOccurrenceCount remaining item))
        calc
          (occurrenceCount (event :: remaining) item : Coordinate) -
                (pairOccurrenceCount (event :: remaining) item : Coordinate) =
              1 - (pairOccurrenceCount remaining item : Coordinate) := by
            simp only [occurrenceCount, pairOccurrenceCount, selected,
              ↓reduceIte, Nat.cast_add, Nat.cast_one]
            ring1
          _ ≤ 1 := sub_le_self 1 pairNonnegative
          _ = Distribution.indicator
                (unionEvents (event :: remaining)) item := by
            simp only [unionEvents, unionEvent, selected, Bool.true_or,
              Distribution.indicator]

namespace Distribution

/-- Sum of intersection probabilities over the unordered pairs of positions
in a displayed event list. -/
def pairIntersectionProbabilitySum {α : Type}
    (distribution : Distribution α) : List (α → Bool) → Coordinate
  | [] => 0
  | event :: remaining =>
      (remaining.map fun candidate =>
        distribution.probability
          (intersectionEvent event candidate)).sum +
        distribution.pairIntersectionProbabilitySum remaining

/-- Recursive positional certificate that every head event is independent of
every later event, and the same holds in the tail. -/
def PairwiseIndependentEventList {α : Type}
    (distribution : Distribution α) : List (α → Bool) → Prop
  | [] => True
  | event :: remaining =>
      (∀ candidate, candidate ∈ remaining →
        distribution.IndependentEvents event candidate) ∧
      distribution.PairwiseIndependentEventList remaining

/-- Multiplying one indicator by the remaining occurrence count integrates
to the sum of the corresponding intersection probabilities. -/
theorem expectation_indicator_mul_occurrenceCount {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (remaining : List (α → Bool)) :
    distribution.expectation (fun item =>
        Distribution.indicator event item *
          (occurrenceCount remaining item : Coordinate)) =
      (remaining.map fun candidate =>
        distribution.probability
          (intersectionEvent event candidate)).sum := by
  induction remaining with
  | nil =>
      calc
        distribution.expectation (fun item =>
              Distribution.indicator event item *
                (occurrenceCount [] item : Coordinate)) =
            distribution.expectation (fun _ => (0 : Coordinate)) :=
          distribution.expectation_congr _ _ (fun item => by
            simp only [occurrenceCount, Nat.cast_zero, mul_zero])
        _ = 0 := distribution.expectation_constant 0
  | cons candidate remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              Distribution.indicator event item *
                (occurrenceCount (candidate :: remaining) item :
                  Coordinate)) =
            distribution.expectation (fun item =>
              Distribution.indicator event item *
                  Distribution.indicator candidate item +
                Distribution.indicator event item *
                  (occurrenceCount remaining item : Coordinate)) :=
          distribution.expectation_congr _ _ (fun item => by
            rw [cast_occurrenceCount_cons]
            ring1)
        _ = distribution.probability
                (intersectionEvent event candidate) +
              (remaining.map fun later =>
                distribution.probability
                  (intersectionEvent event later)).sum := by
          rw [distribution.expectation_add,
            distribution.expectation_indicator_mul_indicator,
            inductionHypothesis]
        _ = ((candidate :: remaining).map fun later =>
              distribution.probability
                (intersectionEvent event later)).sum := by
          rfl

/-- The expected number of occurring unordered pairs is exactly the sum of
their displayed intersection probabilities. -/
theorem expectation_pairOccurrenceCount {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.expectation (fun item =>
        (pairOccurrenceCount events item : Coordinate)) =
      distribution.pairIntersectionProbabilitySum events := by
  induction events with
  | nil =>
      change distribution.expectation (fun _ => (0 : Coordinate)) = 0
      exact distribution.expectation_constant 0
  | cons event remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              (pairOccurrenceCount (event :: remaining) item :
                Coordinate)) =
            distribution.expectation (fun item =>
              Distribution.indicator event item *
                  (occurrenceCount remaining item : Coordinate) +
                (pairOccurrenceCount remaining item : Coordinate)) :=
          distribution.expectation_congr _ _
            (cast_pairOccurrenceCount_cons event remaining)
        _ = distribution.pairIntersectionProbabilitySum
              (event :: remaining) := by
          rw [distribution.expectation_add,
            distribution.expectation_indicator_mul_occurrenceCount event
              remaining,
            inductionHypothesis]
          rfl

/-- Exact second-moment expansion of a finite event occurrence count. -/
theorem expectation_occurrenceCount_sq {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.expectation (fun item =>
        (occurrenceCount events item : Coordinate) ^ 2) =
      (events.map distribution.probability).sum +
        2 * distribution.pairIntersectionProbabilitySum events := by
  induction events with
  | nil =>
      calc
        distribution.expectation (fun item : α =>
              (occurrenceCount ([] : List (α → Bool)) item :
                Coordinate) ^ 2) =
            distribution.expectation (fun _ : α => (0 : Coordinate)) :=
          distribution.expectation_congr _ _ (fun _ => by
            change (0 : Coordinate) ^ 2 = 0
            ring1)
        _ = 0 := distribution.expectation_constant 0
        _ = ([].map distribution.probability).sum +
              2 * distribution.pairIntersectionProbabilitySum [] := by
          simp only [List.map_nil, List.sum_nil,
            pairIntersectionProbabilitySum, mul_zero, add_zero]
  | cons event remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              (occurrenceCount (event :: remaining) item : Coordinate) ^ 2) =
            distribution.expectation (fun item =>
              Distribution.indicator event item +
                2 * (Distribution.indicator event item *
                  (occurrenceCount remaining item : Coordinate)) +
                (occurrenceCount remaining item : Coordinate) ^ 2) :=
          distribution.expectation_congr _ _ (fun item => by
            rw [cast_occurrenceCount_cons]
            cases selected : event item <;>
              simp only [Distribution.indicator, selected] <;> ring1)
        _ = ((event :: remaining).map distribution.probability).sum +
              2 * distribution.pairIntersectionProbabilitySum
                (event :: remaining) := by
          rw [distribution.expectation_add,
            distribution.expectation_add,
            distribution.expectation_indicator,
            distribution.expectation_scale,
            distribution.expectation_indicator_mul_occurrenceCount event
              remaining,
            inductionHypothesis]
          simp only [List.map_cons, List.sum_cons,
            pairIntersectionProbabilitySum]
          ring1

/-- Second Bonferroni inequality for a displayed finite event family. -/
theorem probability_unionEvents_lower_bonferroni_two {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    (events.map distribution.probability).sum -
        distribution.pairIntersectionProbabilitySum events ≤
      distribution.probability (unionEvents events) := by
  have averaged := distribution.expectation_mono
    (fun item => (occurrenceCount events item : Coordinate) -
      (pairOccurrenceCount events item : Coordinate))
    (Distribution.indicator (unionEvents events)) (by
      intro atom member
      exact occurrenceCount_sub_pairOccurrenceCount_le_indicator_union
        events atom.item)
  rw [distribution.expectation_sub,
    distribution.expectation_occurrenceCount events,
    distribution.expectation_pairOccurrenceCount events,
    distribution.expectation_indicator] at averaged
  exact averaged

private theorem intersectionProbabilitySum_eq_mul_probabilitySum
    {α : Type} (distribution : Distribution α) (event : α → Bool) :
    ∀ remaining : List (α → Bool),
      (∀ candidate, candidate ∈ remaining →
        distribution.IndependentEvents event candidate) →
      (remaining.map fun candidate => distribution.probability
          (intersectionEvent event candidate)).sum =
        distribution.probability event *
          (remaining.map distribution.probability).sum
  | [], independent => by
      simp only [List.map_nil, List.sum_nil, mul_zero]
  | candidate :: remaining, independent => by
      have head := independent candidate List.mem_cons_self
      have tail : ∀ later, later ∈ remaining →
          distribution.IndependentEvents event later :=
        fun later member =>
          independent later (List.mem_cons_of_mem candidate member)
      simp only [List.map_cons, List.sum_cons]
      rw [head,
        distribution.intersectionProbabilitySum_eq_mul_probabilitySum
          event remaining tail]
      ring1

/-- The indicator of one event has zero covariance with the count of a
displayed tail whose members are all independent of it. -/
theorem covariance_indicator_occurrenceCount_eq_zero_of_independent
    {α : Type} (distribution : Distribution α) (event : α → Bool)
    (remaining : List (α → Bool))
    (independent : ∀ candidate, candidate ∈ remaining →
      distribution.IndependentEvents event candidate) :
    distribution.covariance (indicator event) (fun item =>
      (occurrenceCount remaining item : Coordinate)) = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_indicator_mul_occurrenceCount event remaining,
    distribution.expectation_indicator,
    distribution.expectation_occurrenceCount remaining,
    distribution.intersectionProbabilitySum_eq_mul_probabilitySum
      event remaining independent]
  ring1

/-- Variance of a count of positionally pairwise-independent events is the
sum of their Bernoulli variances. -/
theorem variance_occurrenceCount_of_pairwiseIndependentEventList
    {α : Type} (distribution : Distribution α)
    (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events) :
    distribution.variance (fun item =>
        (occurrenceCount events item : Coordinate)) =
      (events.map fun event => distribution.probability event *
        (1 - distribution.probability event)).sum := by
  induction events with
  | nil =>
      change distribution.variance (fun _ : α => (0 : Coordinate)) = 0
      exact distribution.variance_constant 0
  | cons event remaining inductionHypothesis =>
      calc
        distribution.variance (fun item =>
              (occurrenceCount (event :: remaining) item : Coordinate)) =
            distribution.variance (fun item =>
              indicator event item +
                (occurrenceCount remaining item : Coordinate)) :=
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
          simp only [List.map_cons, List.sum_cons, mul_zero, add_zero]

private theorem bernoulliVarianceSum_le_probabilitySum
    {α : Type} (distribution : Distribution α) :
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
        exact sub_le_self 1 probabilityNonnegative
      have headBound : probability * (1 - probability) ≤ probability := by
        calc
          probability * (1 - probability) ≤ probability * 1 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              complementFactorLeOne probabilityNonnegative
          _ = probability := by ring1
      simpa only [List.map_cons, List.sum_cons] using
        add_le_add headBound
          (distribution.bernoulliVarianceSum_le_probabilitySum remaining)

/-- Pairwise independence bounds the occurrence-count second moment by
`S + S²`, where `S` is the displayed sum of event probabilities. -/
theorem expectation_occurrenceCount_sq_le_sum_add_sq_of_pairwiseIndependent
    {α : Type} (distribution : Distribution α)
    (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events) :
    distribution.expectation (fun item =>
        (occurrenceCount events item : Coordinate) ^ 2) ≤
      (events.map distribution.probability).sum +
        (events.map distribution.probability).sum ^ 2 := by
  let count : α → Coordinate := fun item =>
    (occurrenceCount events item : Coordinate)
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
          (occurrenceCount events item : Coordinate) ^ 2) =
        distribution.variance count + sum ^ 2 := by
      rw [varianceIdentity, countMean]
      dsimp only [count]
      ring1
    _ = (events.map fun event => distribution.probability event *
          (1 - distribution.probability event)).sum + sum ^ 2 := by
      rw [varianceFormula]
    _ ≤ sum + sum ^ 2 := add_le_add varianceSumBound le_rfl

private theorem aboveFractionZero_occurrenceCount_eq_unionEvents
    {α : Type} (distribution : Distribution α)
    (events : List (α → Bool)) (item : α) :
    distribution.aboveFractionOfMeanEvent
        (fun item => (occurrenceCount events item : Coordinate)) 0 item =
      unionEvents events item := by
  calc
    distribution.aboveFractionOfMeanEvent
          (fun item => (occurrenceCount events item : Coordinate)) 0 item =
        atLeastOccurrences 1 events item := by
      unfold aboveFractionOfMeanEvent atLeastOccurrences
      simp only [zero_mul]
      cases countEq : occurrenceCount events item with
      | zero =>
          simp only [Nat.cast_zero]
          decide
      | succ count =>
          have castPositive :
              0 < ((Nat.succ count : Nat) : Coordinate) :=
            RFAP.ConstructiveFraction.natCast_pos_direct
              (Nat.zero_lt_succ count)
          have oneLe : 1 ≤ Nat.succ count := Nat.succ_le_succ (Nat.zero_le _)
          rw [decide_eq_true_eq.mpr castPositive,
            decide_eq_true_eq.mpr oneLe]
    _ = unionEvents events item :=
      atLeastOccurrences_one_eq_unionEvents events item

/-- Constructive finite second-moment lower bound for a displayed event
union. -/
theorem secondMoment_union_lower_bound {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
    (positive : 0 < (events.map distribution.probability).sum) :
    (events.map distribution.probability).sum ^ 2 /
        ((events.map distribution.probability).sum +
          2 * distribution.pairIntersectionProbabilitySum events) ≤
      distribution.probability (unionEvents events) := by
  have countNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ (occurrenceCount events atom.item : Coordinate) := by
    intro atom member
    simpa only [Nat.cast_zero] using
      RFAP.ConstructiveFraction.natCast_le_direct
        (Nat.zero_le (occurrenceCount events atom.item))
  have meanPositive : 0 < distribution.expectation (fun item =>
      (occurrenceCount events item : Coordinate)) := by
    rw [distribution.expectation_occurrenceCount events]
    exact positive
  have bound := distribution.paleyZygmund_bound
    (fun item => (occurrenceCount events item : Coordinate)) 0
    le_rfl (by decide) countNonnegative meanPositive
  have eventProbability :
      distribution.probability
          (distribution.aboveFractionOfMeanEvent
            (fun item => (occurrenceCount events item : Coordinate)) 0) =
        distribution.probability (unionEvents events) :=
    distribution.probability_congr _ _
      (aboveFractionZero_occurrenceCount_eq_unionEvents distribution events)
  rw [distribution.expectation_occurrenceCount events,
    distribution.expectation_occurrenceCount_sq events,
    eventProbability]
    at bound
  have coefficient : (1 - (0 : Coordinate)) ^ 2 = 1 := by ring1
  rw [coefficient, one_mul] at bound
  exact bound

/-- Division-free pairwise-independent finite union estimate.  It remains
meaningful when the displayed probability sum is zero. -/
theorem pairwiseIndependent_union_lower_mul {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
    (independent : distribution.PairwiseIndependentEventList events) :
    (events.map distribution.probability).sum ^ 2 ≤
      ((events.map distribution.probability).sum +
          (events.map distribution.probability).sum ^ 2) *
        distribution.probability (unionEvents events) := by
  let count : α → Coordinate := fun item =>
    (occurrenceCount events item : Coordinate)
  have countNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ count atom.item := by
    intro atom member
    dsimp only [count]
    simpa only [Nat.cast_zero] using
      RFAP.ConstructiveFraction.natCast_le_direct
        (Nat.zero_le (occurrenceCount events atom.item))
  have multiplicative := distribution.paleyZygmund_mul
    (distribution.aboveFractionOfMeanEvent count 0) count 0 le_rfl
    (by decide) countNonnegative (by
      intro atom atomMember outside
      unfold aboveFractionOfMeanEvent at outside
      have notPositive := decide_eq_false_iff_not.mp outside
      dsimp only [count] at notPositive ⊢
      simpa only [zero_mul] using
        RFAP.ConstructiveFraction.le_of_not_gt_direct notPositive)
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
      exact aboveFractionZero_occurrenceCount_eq_unionEvents
        distribution events item)
  rw [show distribution.expectation count =
      (events.map distribution.probability).sum by
        exact distribution.expectation_occurrenceCount events,
    show distribution.expectation (fun item => count item ^ 2) =
      distribution.expectation (fun item =>
        (occurrenceCount events item : Coordinate) ^ 2) by rfl,
    eventProbability]
      at multiplicative
  have coefficient : (1 - (0 : Coordinate)) ^ 2 = 1 := by ring1
  rw [coefficient, one_mul] at multiplicative
  exact multiplicative.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      secondMomentBound probabilityNonnegative)

/-- Familiar divided form of the finite pairwise-independent union bound:
if `S > 0`, then `S / (1 + S) ≤ P(⋃ Aᵢ)`. -/
theorem pairwiseIndependent_union_lower_bound {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
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
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := sum)
    · calc
        sum * sum = sum ^ 2 := by ring1
        _ ≤ (sum + sum ^ 2) * unionProbability := multiplicative
        _ = (unionProbability * (1 + sum)) * sum := by ring1
    · exact positive
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
  exact cancelled

end Distribution

end FiniteMeasure
