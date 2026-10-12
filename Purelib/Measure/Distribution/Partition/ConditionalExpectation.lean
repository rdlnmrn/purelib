module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
public import Purelib.Measure.Distribution.Conditioning.Moments
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Partition.Expectation
public import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Event.Family
import Purelib.Measure.Event.IndicatorFamily
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat Purelib.Data.List

namespace PositiveEventPartition

/-- Sum each retained partition indicator multiplied by that cell's original conditional mean.

On original distribution occurrences the disjoint covering cells select exactly one conditional mean. The exact finite
event list determines the formula at every payload. -/
@[expose]
def conditionalExpectation {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) : α → Fraction.Rational :=
  fun item =>
    (partition.events.map fun event =>
      Distribution.indicator event item *
        distribution.conditionalMean event value).sum

/-- Pointwise equal observables give equal conditional-expectation values at the supplied payload. -/
theorem conditionalExpectation_congr {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) (item : α) :
    partition.conditionalExpectation left item =
      partition.conditionalExpectation right item := by
  unfold conditionalExpectation
  induction partition.events with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [distribution.conditionalMean_congr event left right pointwise,
        inductionHypothesis]

/-- The finite indicator-weighted conditional-mean sum preserves addition of observables. -/
private theorem conditionalExpectationSum_add {α : Type}
    (distribution : Distribution α) (item : α)
    (left right : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fun candidate => left candidate + right candidate)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event left).sum +
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event right).sum
  | [] => by simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil, zero_add]; try rfl
  | event :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [distribution.conditionalMean_add,
        conditionalExpectationSum_add distribution item left right remaining]
      ring1

/-- The finite indicator-weighted conditional-mean sum preserves subtraction of observables. -/
private theorem conditionalExpectationSum_sub {α : Type}
    (distribution : Distribution α) (item : α)
    (left right : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fun candidate => left candidate - right candidate)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event left).sum -
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event right).sum
  | [] => by simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil, sub_self]; try rfl
  | event :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [distribution.conditionalMean_sub,
        conditionalExpectationSum_sub distribution item left right remaining]
      ring1

/-- The finite indicator-weighted conditional-mean sum preserves scalar multiplication. -/
private theorem conditionalExpectationSum_scale {α : Type}
    (distribution : Distribution α) (item : α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fun candidate => factor * value candidate)).sum =
      factor * (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event value).sum
  | [] => by simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil, mul_zero]; try rfl
  | event :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [distribution.conditionalMean_scale,
        conditionalExpectationSum_scale distribution item factor value
          remaining]
      ring1

/-- Conditional expectation on the retained partition preserves addition pointwise. -/
theorem conditionalExpectation_add {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) (item : α) :
    partition.conditionalExpectation
        (fun candidate => left candidate + right candidate) item =
      partition.conditionalExpectation left item +
        partition.conditionalExpectation right item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_add distribution item left right
    partition.events

/-- Conditional expectation on the retained partition preserves subtraction pointwise. -/
theorem conditionalExpectation_sub {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) (item : α) :
    partition.conditionalExpectation
        (fun candidate => left candidate - right candidate) item =
      partition.conditionalExpectation left item -
        partition.conditionalExpectation right item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_sub distribution item left right
    partition.events

/-- Conditional expectation on the retained partition preserves rational scaling pointwise. -/
theorem conditionalExpectation_scale {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) (item : α) :
    partition.conditionalExpectation
        (fun candidate => factor * value candidate) item =
      factor * partition.conditionalExpectation value item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_scale distribution item factor value
    partition.events

/-- On a retained occurrence, a selected event in a disjoint list determines the entire indicator-weighted
conditional-mean sum. -/
private theorem conditionalMeanIndicatorSum_of_selected
    {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) (atom : Weighted α)
    (atomMember : atom ∈ distribution.atoms) :
    ∀ (events : List (α → Bool)),
      MutuallyDisjointOn distribution.atoms events →
      ∀ (target : α → Bool), target ∈ events →
        target atom.item = true →
        (events.map fun event =>
          Distribution.indicator event atom.item *
            distribution.conditionalMean event value).sum =
          distribution.conditionalMean target value
  | [], disjoint, target, member, selected => by cases member
  | event :: remaining, disjoint, target, member, selected => by
      rcases Membership.mem_cons.mp member with same | tailMember
      · subst target
        have tailUnionFalse : unionEvents remaining atom.item = false := by
          cases tailSelected : unionEvents remaining atom.item
          · rfl
          · exact (disjoint.1 atom atomMember
              ⟨selected, tailSelected⟩).elim
        simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
        have headIndicator : Distribution.indicator event atom.item = 1 := by
          simp only [-eq_self, -iff_self, Distribution.indicator, selected]; try rfl
        rw [headIndicator, one_mul]
        have tailSum :=
          indicatorWeightedSum_eq_zero_of_unionEvents_false atom.item
            (fun candidate => distribution.conditionalMean candidate value)
            remaining tailUnionFalse
        rw [tailSum, add_zero]
      · have tailUnionTrue : unionEvents remaining atom.item = true := by
          cases unionSelected : unionEvents remaining atom.item
          · have targetFalse := event_eq_false_of_mem_of_unionEvents_eq_false
              remaining target tailMember atom.item unionSelected
            exact Bool.noConfusion (targetFalse.symm.trans selected)
          · rfl
        have headFalse : event atom.item = false := by
          cases headSelected : event atom.item
          · rfl
          · exact (disjoint.1 atom atomMember
              ⟨headSelected, tailUnionTrue⟩).elim
        simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons, Distribution.indicator,
          headFalse, zero_mul, zero_add]; try rfl
        exact conditionalMeanIndicatorSum_of_selected distribution value atom
          atomMember remaining disjoint.2 target tailMember selected

/-- At a retained occurrence selected by a partition cell, conditional expectation equals that exact cell's conditional
mean. -/
theorem conditionalExpectation_eq_conditionalMean_on_cell {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (event : α → Bool)
    (eventMember : event ∈ partition.events) (atom : Weighted α)
    (atomMember : atom ∈ distribution.atoms)
    (selected : event atom.item = true) :
    partition.conditionalExpectation value atom.item =
      distribution.conditionalMean event value := by
  unfold conditionalExpectation
  exact conditionalMeanIndicatorSum_of_selected distribution value atom
    atomMember partition.events partition.disjoint event eventMember selected

/-- Expectation of the finite conditional-mean indicator sum equals the corresponding probability-weighted mean sum. -/
private theorem expectation_conditionalMeanIndicators
    {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      distribution.expectation (fun item =>
          (events.map fun event =>
            Distribution.indicator event item *
              distribution.conditionalMean event value).sum) =
        (events.map fun event =>
          distribution.probability event *
            distribution.conditionalMean event value).sum
  | [] => by
      simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil]; try rfl
      exact distribution.expectation_constant 0
  | event :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [distribution.expectation_add,
        distribution.expectation_indicator_mul_constant,
        expectation_conditionalMeanIndicators distribution value remaining]

/-- For positive-probability events, conditional means of a constant sum to the event indicator sum times that constant.
-/
private theorem conditionalMeanIndicators_constant
    {α : Type} (distribution : Distribution α)
    (item : α) (constant : Fraction.Rational) :
    ∀ (events : List (α → Bool)),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event =>
        Distribution.indicator event item *
          distribution.conditionalMean event (fun _ => constant)).sum =
        sumIndicators events item * constant
  | [], positive => by
      simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil, sumIndicators, zero_mul]; try rfl
  | event :: remaining, positive => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons, sumIndicators]; try rfl
      rw [distribution.conditionalMean_constant event
        (positive event List.mem_cons_self) constant]
      rw [conditionalMeanIndicators_constant distribution item constant
        remaining (fun candidate member =>
          positive candidate (List.mem_cons_of_mem event member))]
      ring1

/-- Conditional expectation preserves a constant at every original distribution occurrence. -/
theorem conditionalExpectation_constant_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (constant : Fraction.Rational) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation (fun _ => constant) atom.item =
      constant := by
  unfold conditionalExpectation
  rw [conditionalMeanIndicators_constant distribution atom.item constant
    partition.events partition.positive]
  have sumOne := partition.toEventPartition.sumIndicators_eq_one atom member
  change sumIndicators partition.events atom.item = 1 at sumOne
  rw [sumOne]
  ring1

/-- Pointwise order on original occurrences gives order of partition conditional expectations there. -/
theorem conditionalExpectation_mono_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      lower atom.item ≤ upper atom.item)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation lower atom.item ≤
      partition.conditionalExpectation upper atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      lower event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      upper event eventMember atom member selected]
  exact distribution.conditionalMean_mono event
    (partition.positive event eventMember) lower upper pointwise

/-- An observable nonnegative on original occurrences has nonnegative partition conditional expectation there. -/
theorem conditionalExpectation_nonneg_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    0 ≤ partition.conditionalExpectation value atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
    value event eventMember atom member selected]
  exact distribution.conditionalMean_nonneg event
    (partition.positive event eventMember) value nonnegative

/-- A constant lower bound on original occurrences also bounds their partition conditional expectations. -/
theorem constant_le_conditionalExpectation_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (floor : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      floor ≤ value atom.item)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    floor ≤ partition.conditionalExpectation value atom.item := by
  rw [← partition.conditionalExpectation_constant_on_atoms floor atom member]
  exact partition.conditionalExpectation_mono_on_atoms
    (fun _ => floor) value bounded atom member

/-- A constant upper bound on original occurrences also bounds their partition conditional expectations. -/
theorem conditionalExpectation_le_constant_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      value atom.item ≤ ceiling)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation value atom.item ≤ ceiling := by
  rw [← partition.conditionalExpectation_constant_on_atoms ceiling atom
    member]
  exact partition.conditionalExpectation_mono_on_atoms
    value (fun _ => ceiling) bounded atom member

/-- On a finite positive-probability event list, the probability-weighted conditional means sum to the exact
event-integral sum. -/
private theorem weightedConditionalMeans_eq_eventIntegrals
    {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    ∀ (events : List (α → Bool)),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event =>
          distribution.probability event *
            distribution.conditionalMean event value).sum =
        (events.map fun event =>
          distribution.eventIntegral event value).sum
  | [], positive => rfl
  | event :: remaining, positive => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [distribution.probability_mul_conditionalMean event value
        (positive event List.mem_cons_self)]
      rw [weightedConditionalMeans_eq_eventIntegrals distribution value
        remaining (fun candidate member =>
          positive candidate (List.mem_cons_of_mem event member))]

/-- The probability-weighted conditional means of the retained positive partition sum to the original expectation. -/
theorem total_expectation {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.probability event *
          distribution.conditionalMean event value).sum =
      distribution.expectation value := by
  rw [weightedConditionalMeans_eq_eventIntegrals distribution value
    partition.events partition.positive]
  exact partition.toEventPartition.total_expectation value

/-- Partition conditional expectation preserves the original observable integral on every retained partition cell. -/
theorem eventIntegral_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.eventIntegral event
        (partition.conditionalExpectation value) =
      distribution.eventIntegral event value := by
  calc
    distribution.eventIntegral event
          (partition.conditionalExpectation value) =
        distribution.expectation (fun item =>
          Distribution.indicator event item *
            distribution.conditionalMean event value) := by
      unfold Distribution.eventIntegral
      apply distribution.expectation_congr_off_zero
      intro atom atomMember
      apply Or.inr
      cases selected : event atom.item
      · simp only [-eq_self, -iff_self, Distribution.indicator, selected, zero_mul]; try rfl
      · simp only [-eq_self, -iff_self, Distribution.indicator, selected, one_mul]; try rfl
        exact partition.conditionalExpectation_eq_conditionalMean_on_cell
          value event eventMember atom atomMember selected
    _ = distribution.probability event *
          distribution.conditionalMean event value :=
      distribution.expectation_indicator_mul_constant event
        (distribution.conditionalMean event value)
    _ = distribution.eventIntegral event value :=
      distribution.probability_mul_conditionalMean event value
        (partition.positive event eventMember)

/-- Taking a retained cell's conditional mean after partition conditional expectation preserves its original conditional
mean. -/
theorem conditionalMean_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.conditionalMean event
        (partition.conditionalExpectation value) =
      distribution.conditionalMean event value := by
  unfold Distribution.conditionalMean
  rw [partition.eventIntegral_conditionalExpectation value event eventMember]

/-- Partition conditional expectation has zero conditional variance on each exact retained cell. -/
theorem conditionalVariance_conditionalExpectation_eq_zero {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.conditionalVariance event
        (partition.conditionalExpectation value) = 0 := by
  unfold Distribution.conditionalVariance
  rw [partition.conditionalMean_conditionalExpectation value event
    eventMember]
  unfold Distribution.conditionalMean
  have numeratorZero :
      distribution.eventIntegral event (fun item =>
        (partition.conditionalExpectation value item -
          distribution.eventIntegral event value /
            distribution.probability event) ^ 2) = 0 := by
    unfold Distribution.eventIntegral
    calc
      distribution.expectation (fun item => Distribution.indicator event item *
            (partition.conditionalExpectation value item -
              distribution.eventIntegral event value /
                distribution.probability event) ^ 2) =
          distribution.expectation (fun _ => 0) := by
        apply distribution.expectation_congr_off_zero
        intro atom atomMember
        apply Or.inr
        cases selected : event atom.item
        · simp only [-eq_self, -iff_self, Distribution.indicator, selected, zero_mul]; try rfl
        · simp only [-eq_self, -iff_self, Distribution.indicator, selected, one_mul]; try rfl
          rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
            value event eventMember atom atomMember selected]
          unfold Distribution.conditionalMean
          ring1
      _ = 0 := by
        rw [distribution.expectation_constant]
  rw [numeratorZero]
  exact Fraction.Field.zero_div_direct _

/-- Reconditioning the observable leaves every indicator-weighted mean sum over retained partition cells unchanged. -/
private theorem conditionalExpectationSum_idempotent {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (item : α) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (partition.conditionalExpectation value)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event value).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]; try rfl
      rw [partition.conditionalMean_conditionalExpectation value event
        (subset event List.mem_cons_self)]
      rw [conditionalExpectationSum_idempotent partition value item remaining
        (fun candidate member =>
          subset candidate (List.mem_cons_of_mem event member))]

/-- Applying the same finite partition conditional expectation twice gives the same value at every payload. -/
theorem conditionalExpectation_idempotent {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (item : α) :
    partition.conditionalExpectation
        (partition.conditionalExpectation value) item =
      partition.conditionalExpectation value item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_idempotent partition value item
    partition.events (fun event member => member)

/-- Finite partition conditional expectation preserves the original distribution's total expectation. -/
theorem expectation_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    distribution.expectation (partition.conditionalExpectation value) =
      distribution.expectation value := by
  change distribution.expectation (fun item =>
      (partition.events.map fun event =>
        Distribution.indicator event item *
          distribution.conditionalMean event value).sum) =
    distribution.expectation value
  rw [expectation_conditionalMeanIndicators distribution value]
  exact partition.total_expectation value
end PositiveEventPartition

end Purelib.Measure

end
