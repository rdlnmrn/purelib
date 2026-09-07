import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Conditioning
import FiniteMeasure.Stability

/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

namespace FiniteMeasure

/-- Pointwise sum of the rational indicators of a displayed event list. -/
def sumIndicators {α : Type} : List (α → Bool) → α → Coordinate
  | [], _ => 0
  | event :: remaining, item =>
      Distribution.indicator event item + sumIndicators remaining item

/-- On displayed atoms, pairwise disjointness makes the sum of indicators
equal the indicator of the displayed finite union. -/
theorem sumIndicators_eq_indicator_unionEvents_of_disjoint
    {α : Type} (atoms : List (Weighted α)) :
    ∀ {events : List (α → Bool)},
      MutuallyDisjointOn atoms events →
      ∀ (atom : Weighted α), atom ∈ atoms →
        sumIndicators events atom.item =
          Distribution.indicator (unionEvents events) atom.item
  | [], _, atom, member => by
      simp only [sumIndicators, unionEvents, Distribution.indicator]
  | event :: remaining, disjoint, atom, member => by
      have tail := sumIndicators_eq_indicator_unionEvents_of_disjoint
        atoms disjoint.2 atom member
      cases headSelected : event atom.item <;>
        cases tailSelected : unionEvents remaining atom.item
      · simp only [sumIndicators, Distribution.indicator, headSelected,
          tailSelected, unionEvents, unionEvent, Bool.false_or, tail,
          zero_add]
      · simp only [sumIndicators, Distribution.indicator, headSelected,
          tailSelected, unionEvents, unionEvent, Bool.false_or, tail,
          zero_add]
      · simp only [sumIndicators, Distribution.indicator, headSelected,
          tailSelected, unionEvents, unionEvent, Bool.true_or, tail,
          add_zero]
      · exact (disjoint.1 atom member
          ⟨headSelected, tailSelected⟩).elim

namespace Distribution

/-- Exact rational integral of an observable restricted to one displayed
Boolean event. -/
def eventIntegral {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Coordinate) : Coordinate :=
  distribution.expectation fun item => indicator event item * value item

/-- Pointwise-equal observables have the same integral on an event. -/
theorem eventIntegral_congr {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    distribution.eventIntegral event left =
      distribution.eventIntegral event right := by
  unfold eventIntegral
  exact distribution.expectation_congr _ _ (fun item =>
    congrArg (fun value => indicator event item * value) (pointwise item))

theorem eventIntegral_add {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate) :
    distribution.eventIntegral event (fun item => left item + right item) =
      distribution.eventIntegral event left +
        distribution.eventIntegral event right := by
  unfold eventIntegral
  calc
    distribution.expectation (fun item =>
        indicator event item * (left item + right item)) =
        distribution.expectation (fun item =>
          indicator event item * left item +
            indicator event item * right item) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          indicator event item * left item) +
        distribution.expectation (fun item =>
          indicator event item * right item) :=
      distribution.expectation_add _ _

theorem eventIntegral_sub {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate) :
    distribution.eventIntegral event (fun item => left item - right item) =
      distribution.eventIntegral event left -
        distribution.eventIntegral event right := by
  unfold eventIntegral
  calc
    distribution.expectation (fun item =>
        indicator event item * (left item - right item)) =
        distribution.expectation (fun item =>
          indicator event item * left item -
            indicator event item * right item) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          indicator event item * left item) -
        distribution.expectation (fun item =>
          indicator event item * right item) :=
      distribution.expectation_sub _ _

theorem eventIntegral_scale {α : Type} (distribution : Distribution α)
    (event : α → Bool) (factor : Coordinate)
    (value : α → Coordinate) :
    distribution.eventIntegral event (fun item => factor * value item) =
      factor * distribution.eventIntegral event value := by
  unfold eventIntegral
  calc
    distribution.expectation (fun item =>
        indicator event item * (factor * value item)) =
        distribution.expectation (fun item =>
          factor * (indicator event item * value item)) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = factor * distribution.expectation (fun item =>
          indicator event item * value item) :=
      distribution.expectation_scale _ _

theorem eventIntegral_constant {α : Type} (distribution : Distribution α)
    (event : α → Bool) (constant : Coordinate) :
    distribution.eventIntegral event (fun _ => constant) =
      distribution.probability event * constant := by
  unfold eventIntegral
  exact distribution.expectation_indicator_mul_constant event constant

/-- Linearity expands a displayed finite sum of restricted integrals into
one integral against the pointwise sum of indicators. -/
theorem eventIntegrals_sum {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    ∀ events : List (α → Bool),
      (events.map fun event => distribution.eventIntegral event value).sum =
        distribution.expectation fun item =>
          sumIndicators events item * value item
  | [] => by
      simp only [List.map_nil, List.sum_nil]
      calc
        0 = distribution.expectation (fun _ => 0) :=
          (distribution.expectation_constant 0).symm
        _ = distribution.expectation (fun item =>
              sumIndicators [] item * value item) :=
          distribution.expectation_congr _ _ (fun item => by
            simp only [sumIndicators, zero_mul])
  | event :: remaining => by
      rw [List.map_cons, List.sum_cons,
        eventIntegrals_sum distribution value remaining]
      unfold eventIntegral
      rw [← distribution.expectation_add]
      exact distribution.expectation_congr _ _ (fun item => by
        simp only [sumIndicators]
        ring1)

/-- Restricted integrals over a displayed disjoint event family consume at
most the full expectation of a nonnegative observable. -/
theorem eventIntegrals_sum_le_expectation_of_disjoint_nonnegative
    {α : Type} (distribution : Distribution α)
    (events : List (α → Bool)) (value : α → Coordinate)
    (disjoint : MutuallyDisjointOn distribution.atoms events)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    (events.map fun event => distribution.eventIntegral event value).sum ≤
      distribution.expectation value := by
  calc
    (events.map fun event => distribution.eventIntegral event value).sum =
        distribution.expectation (fun item =>
          sumIndicators events item * value item) :=
      distribution.eventIntegrals_sum value events
    _ = distribution.expectation (fun item =>
          indicator (unionEvents events) item * value item) := by
      apply distribution.expectation_congr_off_zero
      intro atom member
      apply Or.inr
      change sumIndicators events atom.item * value atom.item =
        indicator (unionEvents events) atom.item * value atom.item
      rw [sumIndicators_eq_indicator_unionEvents_of_disjoint
        distribution.atoms disjoint atom member]
    _ ≤ distribution.expectation value := by
      apply distribution.expectation_mono
      intro atom member
      cases selected : unionEvents events atom.item
      · simp only [indicator, selected, zero_mul]
        exact nonnegative atom member
      · simp only [indicator, selected, one_mul]
        exact le_rfl

/-- Rational conditional mean on a displayed event.  Positivity is kept as a
theorem hypothesis rather than hidden in this executable quotient. -/
def conditionalMean {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Coordinate) : Coordinate :=
  distribution.eventIntegral event value /
    distribution.probability event

/-- Pointwise-equal observables have the same conditional mean. -/
theorem conditionalMean_congr {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    distribution.conditionalMean event left =
      distribution.conditionalMean event right := by
  unfold conditionalMean
  exact congrArg (fun numerator =>
      numerator / distribution.probability event)
    (distribution.eventIntegral_congr event left right pointwise)

/-- The expectation of the explicitly conditioned finite distribution is
exactly the rational conditional mean on that event. -/
theorem conditioned_expectation_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    (distribution.conditioned event positive).expectation value =
      distribution.conditionalMean event value := by
  rw [distribution.conditioned_expectation event positive value]
  calc
    distribution.expectation (fun item =>
        distribution.conditioningDensity event positive item * value item) =
        distribution.expectation (fun item =>
          (distribution.probability event)⁻¹ *
            (Distribution.indicator event item * value item)) :=
      distribution.expectation_congr _ _ (fun item => by
        unfold conditioningDensity
        calc
          (Distribution.indicator event item *
                (distribution.probability event)⁻¹) * value item =
              ((distribution.probability event)⁻¹ *
                Distribution.indicator event item) * value item := by
            rw [RFAP.ConstructiveFraction.mul_comm
              (Distribution.indicator event item)
              (distribution.probability event)⁻¹]
          _ = (distribution.probability event)⁻¹ *
                (Distribution.indicator event item * value item) :=
            RFAP.ConstructiveFraction.mul_assoc _ _ _)
    _ = (distribution.probability event)⁻¹ *
          distribution.expectation (fun item =>
            Distribution.indicator event item * value item) :=
      distribution.expectation_scale _ _
    _ = distribution.conditionalMean event value := by
      unfold conditionalMean eventIntegral
      exact RFAP.ConstructiveFraction.mul_comm _ _

theorem eventIntegral_nonneg {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    0 ≤ distribution.eventIntegral event value := by
  unfold eventIntegral
  apply distribution.expectation_nonneg
  intro atom member
  apply RFAP.ConstructiveFraction.mul_nonneg_direct
  · cases selected : event atom.item <;>
      simp only [indicator, selected] <;> decide
  · exact nonnegative atom member

/-- Restricted integration is monotone when the comparison is supplied only
on the selected event, since both restricted integrands vanish outside it. -/
theorem eventIntegral_mono_on_event {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true → lower atom.item ≤ upper atom.item) :
    distribution.eventIntegral event lower ≤
      distribution.eventIntegral event upper := by
  unfold eventIntegral
  apply distribution.expectation_mono
  intro atom member
  cases selected : event atom.item
  · simp only [indicator, selected, zero_mul]
    exact le_rfl
  · simpa only [indicator, selected, one_mul] using
      pointwise atom member selected

theorem conditionalMean_nonneg {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    0 ≤ distribution.conditionalMean event value := by
  unfold conditionalMean
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (distribution.eventIntegral_nonneg event value nonnegative) positive.le

theorem conditionalMean_add {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate) :
    distribution.conditionalMean event (fun item => left item + right item) =
      distribution.conditionalMean event left +
        distribution.conditionalMean event right := by
  unfold conditionalMean
  rw [distribution.eventIntegral_add]
  change (distribution.eventIntegral event left +
      distribution.eventIntegral event right) *
        (distribution.probability event)⁻¹ =
    distribution.eventIntegral event left *
        (distribution.probability event)⁻¹ +
      distribution.eventIntegral event right *
        (distribution.probability event)⁻¹
  exact add_mul _ _ _

theorem conditionalMean_sub {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate) :
    distribution.conditionalMean event (fun item => left item - right item) =
      distribution.conditionalMean event left -
        distribution.conditionalMean event right := by
  unfold conditionalMean
  rw [distribution.eventIntegral_sub]
  change (distribution.eventIntegral event left -
      distribution.eventIntegral event right) *
        (distribution.probability event)⁻¹ =
    distribution.eventIntegral event left *
        (distribution.probability event)⁻¹ -
      distribution.eventIntegral event right *
        (distribution.probability event)⁻¹
  exact sub_mul _ _ _

/-- Conditional averaging preserves a displayed pointwise order. -/
theorem conditionalMean_mono {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      lower atom.item ≤ upper atom.item) :
    distribution.conditionalMean event lower ≤
      distribution.conditionalMean event upper := by
  have differenceNonnegative := distribution.conditionalMean_nonneg event
    positive (fun item => upper item - lower item) (by
      intro atom member
      exact sub_nonneg.mpr (pointwise atom member))
  rw [distribution.conditionalMean_sub] at differenceNonnegative
  exact sub_nonneg.mp differenceNonnegative

/-- Conditional averaging preserves an order supplied only on the selected
event. -/
theorem conditionalMean_mono_on_event {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true → lower atom.item ≤ upper atom.item) :
    distribution.conditionalMean event lower ≤
      distribution.conditionalMean event upper := by
  have numeratorOrder := distribution.eventIntegral_mono_on_event event
    lower upper pointwise
  unfold conditionalMean
  change distribution.eventIntegral event lower *
      (distribution.probability event)⁻¹ ≤
    distribution.eventIntegral event upper *
      (distribution.probability event)⁻¹
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    numeratorOrder
    (RFAP.ConstructiveFraction.inv_pos_direct positive).le

theorem conditionalMean_scale {α : Type} (distribution : Distribution α)
    (event : α → Bool) (factor : Coordinate)
    (value : α → Coordinate) :
    distribution.conditionalMean event (fun item => factor * value item) =
      factor * distribution.conditionalMean event value := by
  unfold conditionalMean
  rw [distribution.eventIntegral_scale]
  change (factor * distribution.eventIntegral event value) *
      (distribution.probability event)⁻¹ =
    factor * (distribution.eventIntegral event value *
      (distribution.probability event)⁻¹)
  exact RFAP.ConstructiveFraction.mul_assoc _ _ _

/-- Multiplying a conditional mean by the positive conditioning probability
recovers the exact restricted integral. -/
theorem probability_mul_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate)
    (positive : 0 < distribution.probability event) :
    distribution.probability event *
        distribution.conditionalMean event value =
      distribution.eventIntegral event value := by
  calc
    distribution.probability event *
          distribution.conditionalMean event value =
        (distribution.eventIntegral event value /
            distribution.probability event) *
          distribution.probability event := by
      unfold conditionalMean
      ring1
    _ = distribution.eventIntegral event value :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne'

/-- The conditional mean of a rational constant on a positive cell is that
constant. -/
theorem conditionalMean_constant {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (constant : Coordinate) :
    distribution.conditionalMean event (fun _ => constant) = constant := by
  unfold conditionalMean eventIntegral
  rw [distribution.expectation_indicator_mul_constant]
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne positive.ne'
  change ((distribution.probability event * constant) /
      distribution.probability event) * distribution.probability event =
    constant * distribution.probability event
  calc
    ((distribution.probability event * constant) /
          distribution.probability event) * distribution.probability event =
        distribution.probability event * constant :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne'
    _ = constant * distribution.probability event := by ring1

/-- Exact squared dispersion inside one displayed conditioning cell. -/
def conditionalVariance {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Coordinate) : Coordinate :=
  distribution.conditionalMean event fun item =>
    (value item - distribution.conditionalMean event value) ^ 2

theorem conditionalVariance_nonneg {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    0 ≤ distribution.conditionalVariance event value := by
  unfold conditionalVariance
  apply distribution.conditionalMean_nonneg event positive
  intro atom member
  exact RFAP.ConstructiveFraction.sq_nonneg_direct _

/-- Conditional variance is conditional second moment minus squared
conditional mean, using only finite rational linearity. -/
theorem conditionalVariance_eq_secondMoment_sub_sq {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    distribution.conditionalVariance event value =
      distribution.conditionalMean event (fun item => value item ^ 2) -
        distribution.conditionalMean event value ^ 2 := by
  unfold conditionalVariance
  calc
    distribution.conditionalMean event (fun item =>
        (value item - distribution.conditionalMean event value) ^ 2) =
        distribution.conditionalMean event (fun item =>
          (value item ^ 2 -
            (2 * distribution.conditionalMean event value) * value item) +
            distribution.conditionalMean event value ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item => by ring1)
    _ = distribution.conditionalMean event (fun item => value item ^ 2) -
          distribution.conditionalMean event value ^ 2 := by
      rw [distribution.conditionalMean_add,
        distribution.conditionalMean_sub, distribution.conditionalMean_scale,
        distribution.conditionalMean_constant event positive]
      ring1

/-- Finite conditional variance-shift identity. -/
theorem conditionalMean_sq_sub_center {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) (center : Coordinate) :
    distribution.conditionalMean event
        (fun item => (value item - center) ^ 2) =
      distribution.conditionalVariance event value +
        (distribution.conditionalMean event value - center) ^ 2 := by
  calc
    distribution.conditionalMean event (fun item =>
        (value item - center) ^ 2) =
        distribution.conditionalMean event (fun item =>
          (value item ^ 2 - (2 * center) * value item) + center ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item => by ring1)
    _ = distribution.conditionalVariance event value +
          (distribution.conditionalMean event value - center) ^ 2 := by
      rw [distribution.conditionalMean_add,
        distribution.conditionalMean_sub, distribution.conditionalMean_scale,
        distribution.conditionalMean_constant event positive,
        distribution.conditionalVariance_eq_secondMoment_sub_sq event positive]
      ring1

end Distribution

namespace EventPartition

/-- Every displayed atom of a finite partition has exactly one unit of
indicator mass across the cells. -/
theorem sumIndicators_eq_one {α : Type} {distribution : Distribution α}
    (partition : EventPartition distribution)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    sumIndicators partition.events atom.item = 1 := by
  rw [sumIndicators_eq_indicator_unionEvents_of_disjoint
    distribution.atoms partition.disjoint atom member]
  simp only [Distribution.indicator, partition.covers atom member]

/-- Every displayed atom is selected by at least one cell of a covering
finite event partition. -/
theorem exists_selected_event {α : Type}
    {distribution : Distribution α}
    (partition : EventPartition distribution)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    ∃ event, event ∈ partition.events ∧ event atom.item = true := by
  have covered := partition.covers atom member
  let item := atom.item
  have findSelected : ∀ (events : List (α → Bool)),
      unionEvents events item = true →
        ∃ event, event ∈ events ∧ event item = true := by
    intro events
    induction events with
    | nil =>
        intro impossible
        simp only [unionEvents] at impossible
        exact Bool.noConfusion impossible
    | cons event remaining inductionHypothesis =>
        intro unionTrue
        cases selected : event item
        · have remainingTrue : unionEvents remaining item = true := by
            simpa only [unionEvents, unionEvent, selected, Bool.false_or]
              using unionTrue
          rcases inductionHypothesis remainingTrue with
            ⟨target, targetMember, targetSelected⟩
          exact ⟨target, List.mem_cons_of_mem event targetMember,
            targetSelected⟩
        · exact ⟨event, List.mem_cons_self, selected⟩
  exact findSelected partition.events covered

/-- Exact finite law of total expectation, stated first as a sum of
restricted rational integrals over a displayed partition. -/
theorem total_expectation {α : Type} {distribution : Distribution α}
    (partition : EventPartition distribution)
    (value : α → Coordinate) :
    (partition.events.map fun event =>
        distribution.eventIntegral event value).sum =
      distribution.expectation value := by
  rw [distribution.eventIntegrals_sum]
  apply distribution.expectation_congr_off_zero
  intro atom member
  apply Or.inr
  change sumIndicators partition.events atom.item * value atom.item =
    value atom.item
  rw [partition.sumIndicators_eq_one atom member]
  ring1

end EventPartition

/-- A finite event partition whose displayed cells all carry positive
rational probability.  This is precisely the certificate needed to divide
by every cell probability constructively. -/
structure PositiveEventPartition {α : Type}
    (distribution : Distribution α) where
  events : List (α → Bool)
  disjoint : MutuallyDisjointOn distribution.atoms events
  covers : ∀ atom, atom ∈ distribution.atoms →
    unionEvents events atom.item = true
  positive : ∀ event, event ∈ events →
    0 < distribution.probability event

namespace PositiveEventPartition

/-- Forget only the positivity certificates. -/
def toEventPartition {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) :
    EventPartition distribution where
  events := partition.events
  disjoint := partition.disjoint
  covers := partition.covers

/-- The finite conditional-expectation observable associated with a
displayed positive event partition.  At each item it sums the partition-cell
indicators multiplied by their exact rational conditional means. -/
def conditionalExpectation {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) : α → Coordinate :=
  fun item =>
    (partition.events.map fun event =>
      Distribution.indicator event item *
        distribution.conditionalMean event value).sum

/-- Pointwise-equal observables have pointwise-equal finite conditional
expectations. -/
theorem conditionalExpectation_congr {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) (item : α) :
    partition.conditionalExpectation left item =
      partition.conditionalExpectation right item := by
  unfold conditionalExpectation
  induction partition.events with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.conditionalMean_congr event left right pointwise,
        inductionHypothesis]

private theorem conditionalExpectationSum_add {α : Type}
    (distribution : Distribution α) (item : α)
    (left right : α → Coordinate) :
    ∀ events : List (α → Bool),
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fun candidate => left candidate + right candidate)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event left).sum +
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event right).sum
  | [] => by simp only [List.map_nil, List.sum_nil, zero_add]
  | event :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.conditionalMean_add,
        conditionalExpectationSum_add distribution item left right remaining]
      ring1

private theorem conditionalExpectationSum_sub {α : Type}
    (distribution : Distribution α) (item : α)
    (left right : α → Coordinate) :
    ∀ events : List (α → Bool),
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fun candidate => left candidate - right candidate)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event left).sum -
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event right).sum
  | [] => by simp only [List.map_nil, List.sum_nil, sub_self]
  | event :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.conditionalMean_sub,
        conditionalExpectationSum_sub distribution item left right remaining]
      ring1

private theorem conditionalExpectationSum_scale {α : Type}
    (distribution : Distribution α) (item : α)
    (factor : Coordinate) (value : α → Coordinate) :
    ∀ events : List (α → Bool),
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fun candidate => factor * value candidate)).sum =
      factor * (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event value).sum
  | [] => by simp only [List.map_nil, List.sum_nil, mul_zero]
  | event :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.conditionalMean_scale,
        conditionalExpectationSum_scale distribution item factor value
          remaining]
      ring1

/-- Finite conditional expectation is exactly additive as a rational
observable. -/
theorem conditionalExpectation_add {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) (item : α) :
    partition.conditionalExpectation
        (fun candidate => left candidate + right candidate) item =
      partition.conditionalExpectation left item +
        partition.conditionalExpectation right item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_add distribution item left right
    partition.events

/-- Finite conditional expectation commutes with rational subtraction. -/
theorem conditionalExpectation_sub {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) (item : α) :
    partition.conditionalExpectation
        (fun candidate => left candidate - right candidate) item =
      partition.conditionalExpectation left item -
        partition.conditionalExpectation right item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_sub distribution item left right
    partition.events

/-- Finite conditional expectation commutes with rational scaling. -/
theorem conditionalExpectation_scale {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (factor : Coordinate) (value : α → Coordinate) (item : α) :
    partition.conditionalExpectation
        (fun candidate => factor * value candidate) item =
      factor * partition.conditionalExpectation value item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_scale distribution item factor value
    partition.events

private theorem unionEvents_eq_true_of_mem {α : Type}
    (item : α) (target : α → Bool) :
    ∀ {events : List (α → Bool)}, target ∈ events →
      target item = true → unionEvents events item = true
  | [], member, selected => by cases member
  | event :: remaining, member, selected => by
      rcases List.mem_cons.mp member with same | tailMember
      · subst target
        simp only [unionEvents, unionEvent, selected, Bool.true_or]
      · rw [unionEvents]
        unfold unionEvent
        rw [unionEvents_eq_true_of_mem item target tailMember selected,
          Bool.or_true]

private theorem indicatorWeightedSum_eq_zero_of_unionEvents_false
    {α : Type} (item : α) (coefficient : (α → Bool) → Coordinate) :
    ∀ events : List (α → Bool), unionEvents events item = false →
      (events.map fun event =>
        Distribution.indicator event item * coefficient event).sum = 0
  | [], unionFalse => rfl
  | event :: remaining, unionFalse => by
      cases selected : event item
      · simp only [List.map_cons, List.sum_cons, Distribution.indicator,
          selected, zero_mul, zero_add]
        apply indicatorWeightedSum_eq_zero_of_unionEvents_false
        simpa only [unionEvents, unionEvent, selected, Bool.false_or]
          using unionFalse
      · simp only [unionEvents, unionEvent, selected, Bool.true_or]
          at unionFalse
        exact Bool.noConfusion unionFalse

private theorem conditionalMeanIndicatorSum_of_selected
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) (atom : Weighted α)
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
      rcases List.mem_cons.mp member with same | tailMember
      · subst target
        have tailUnionFalse : unionEvents remaining atom.item = false := by
          cases tailSelected : unionEvents remaining atom.item
          · rfl
          · exact (disjoint.1 atom atomMember
              ⟨selected, tailSelected⟩).elim
        simp only [List.map_cons, List.sum_cons]
        have headIndicator : Distribution.indicator event atom.item = 1 := by
          simp only [Distribution.indicator, selected]
        rw [headIndicator, one_mul]
        have tailSum :=
          indicatorWeightedSum_eq_zero_of_unionEvents_false atom.item
            (fun candidate => distribution.conditionalMean candidate value)
            remaining tailUnionFalse
        rw [tailSum, add_zero]
      · have tailUnionTrue : unionEvents remaining atom.item = true :=
          unionEvents_eq_true_of_mem atom.item target tailMember selected
        have headFalse : event atom.item = false := by
          cases headSelected : event atom.item
          · rfl
          · exact (disjoint.1 atom atomMember
              ⟨headSelected, tailUnionTrue⟩).elim
        simp only [List.map_cons, List.sum_cons, Distribution.indicator,
          headFalse, zero_mul, zero_add]
        exact conditionalMeanIndicatorSum_of_selected distribution value atom
          atomMember remaining disjoint.2 target tailMember selected

/-- On a displayed atom selected by a partition cell, finite conditional
expectation is exactly that cell's rational conditional mean. -/
theorem conditionalExpectation_eq_conditionalMean_on_cell {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (event : α → Bool)
    (eventMember : event ∈ partition.events) (atom : Weighted α)
    (atomMember : atom ∈ distribution.atoms)
    (selected : event atom.item = true) :
    partition.conditionalExpectation value atom.item =
      distribution.conditionalMean event value := by
  unfold conditionalExpectation
  exact conditionalMeanIndicatorSum_of_selected distribution value atom
    atomMember partition.events partition.disjoint event eventMember selected

private theorem expectation_conditionalMeanIndicators
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    ∀ events : List (α → Bool),
      distribution.expectation (fun item =>
          (events.map fun event =>
            Distribution.indicator event item *
              distribution.conditionalMean event value).sum) =
        (events.map fun event =>
          distribution.probability event *
            distribution.conditionalMean event value).sum
  | [] => by
      simp only [List.map_nil, List.sum_nil]
      exact distribution.expectation_constant 0
  | event :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.expectation_add,
        distribution.expectation_indicator_mul_constant,
        expectation_conditionalMeanIndicators distribution value remaining]

private theorem conditionalMeanIndicators_constant
    {α : Type} (distribution : Distribution α)
    (item : α) (constant : Coordinate) :
    ∀ (events : List (α → Bool)),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event =>
        Distribution.indicator event item *
          distribution.conditionalMean event (fun _ => constant)).sum =
        sumIndicators events item * constant
  | [], positive => by
      simp only [List.map_nil, List.sum_nil, sumIndicators, zero_mul]
  | event :: remaining, positive => by
      simp only [List.map_cons, List.sum_cons, sumIndicators]
      rw [distribution.conditionalMean_constant event
        (positive event List.mem_cons_self) constant]
      rw [conditionalMeanIndicators_constant distribution item constant
        remaining (fun candidate member =>
          positive candidate (List.mem_cons_of_mem event member))]
      ring1

/-- The finite conditional-expectation observable fixes constants on every
displayed atom covered by the partition. -/
theorem conditionalExpectation_constant_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (constant : Coordinate) (atom : Weighted α)
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

/-- Finite conditional expectation preserves pointwise order on every
displayed atom. -/
theorem conditionalExpectation_mono_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (lower upper : α → Coordinate)
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

/-- A nonnegative observable has a nonnegative finite conditional
expectation on every displayed atom. -/
theorem conditionalExpectation_nonneg_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate)
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

/-- A displayed constant lower bound survives finite conditional
expectation. -/
theorem constant_le_conditionalExpectation_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (floor : Coordinate)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      floor ≤ value atom.item)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    floor ≤ partition.conditionalExpectation value atom.item := by
  rw [← partition.conditionalExpectation_constant_on_atoms floor atom member]
  exact partition.conditionalExpectation_mono_on_atoms
    (fun _ => floor) value bounded atom member

/-- A displayed constant upper bound survives finite conditional
expectation. -/
theorem conditionalExpectation_le_constant_on_atoms {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      value atom.item ≤ ceiling)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation value atom.item ≤ ceiling := by
  rw [← partition.conditionalExpectation_constant_on_atoms ceiling atom
    member]
  exact partition.conditionalExpectation_mono_on_atoms
    value (fun _ => ceiling) bounded atom member

private theorem weightedConditionalMeans_eq_eventIntegrals
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
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
      simp only [List.map_cons, List.sum_cons]
      rw [distribution.probability_mul_conditionalMean event value
        (positive event List.mem_cons_self)]
      rw [weightedConditionalMeans_eq_eventIntegrals distribution value
        remaining (fun candidate member =>
          positive candidate (List.mem_cons_of_mem event member))]

/-- Exact rational law of total expectation in conditional-mean form.
Every term and every proof obligation is finite and executable. -/
theorem total_expectation {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    (partition.events.map fun event =>
        distribution.probability event *
          distribution.conditionalMean event value).sum =
      distribution.expectation value := by
  rw [weightedConditionalMeans_eq_eventIntegrals distribution value
    partition.events partition.positive]
  exact partition.toEventPartition.total_expectation value

/-- Conditional expectation preserves the exact restricted integral on
each displayed partition cell.  This is the finite rational analogue of its
defining test-set property. -/
theorem eventIntegral_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (event : α → Bool)
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
      · simp only [Distribution.indicator, selected, zero_mul]
      · simp only [Distribution.indicator, selected, one_mul]
        exact partition.conditionalExpectation_eq_conditionalMean_on_cell
          value event eventMember atom atomMember selected
    _ = distribution.probability event *
          distribution.conditionalMean event value :=
      distribution.expectation_indicator_mul_constant event
        (distribution.conditionalMean event value)
    _ = distribution.eventIntegral event value :=
      distribution.probability_mul_conditionalMean event value
        (partition.positive event eventMember)

/-- Taking the conditional mean of the finite conditional-expectation
observable on one of its own cells recovers the original conditional mean. -/
theorem conditionalMean_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.conditionalMean event
        (partition.conditionalExpectation value) =
      distribution.conditionalMean event value := by
  unfold Distribution.conditionalMean
  rw [partition.eventIntegral_conditionalExpectation value event eventMember]

/-- Conditional variance of a partition-constant conditional expectation
vanishes on each displayed cell. -/
theorem conditionalVariance_conditionalExpectation_eq_zero {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (event : α → Bool)
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
        · simp only [Distribution.indicator, selected, zero_mul]
        · simp only [Distribution.indicator, selected, one_mul]
          rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
            value event eventMember atom atomMember selected]
          unfold Distribution.conditionalMean
          ring1
      _ = 0 := by
        rw [distribution.expectation_constant]
  rw [numeratorZero]
  exact RFAP.ConstructiveFraction.zero_div_direct _

private theorem conditionalExpectationSum_idempotent {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (item : α) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (partition.conditionalExpectation value)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event value).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [partition.conditionalMean_conditionalExpectation value event
        (subset event List.mem_cons_self)]
      rw [conditionalExpectationSum_idempotent partition value item remaining
        (fun candidate member =>
          subset candidate (List.mem_cons_of_mem event member))]

/-- Reapplying conditional expectation for the same displayed positive
partition changes nothing.  This exact finite idempotence is the projection
law behind the same-stage tower intuition. -/
theorem conditionalExpectation_idempotent {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (item : α) :
    partition.conditionalExpectation
        (partition.conditionalExpectation value) item =
      partition.conditionalExpectation value item := by
  unfold conditionalExpectation
  exact conditionalExpectationSum_idempotent partition value item
    partition.events (fun event member => member)

/-- Finite conditional expectation preserves the exact rational
expectation. -/
theorem expectation_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    distribution.expectation (partition.conditionalExpectation value) =
      distribution.expectation value := by
  change distribution.expectation (fun item =>
      (partition.events.map fun event =>
        Distribution.indicator event item *
          distribution.conditionalMean event value).sum) =
    distribution.expectation value
  rw [expectation_conditionalMeanIndicators distribution value]
  exact partition.total_expectation value

private theorem weightedConditionalVariances_eq_eventIntegrals
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) (center : Coordinate) :
    ∀ (events : List (α → Bool)),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event =>
          distribution.probability event *
            (distribution.conditionalVariance event value +
              (distribution.conditionalMean event value - center) ^ 2)).sum =
        (events.map fun event =>
          distribution.eventIntegral event
            (fun item => (value item - center) ^ 2)).sum
  | [], positive => rfl
  | event :: remaining, positive => by
      simp only [List.map_cons, List.sum_cons]
      rw [← distribution.conditionalMean_sq_sub_center event
        (positive event List.mem_cons_self) value center]
      rw [distribution.probability_mul_conditionalMean event
        (fun item => (value item - center) ^ 2)
        (positive event List.mem_cons_self)]
      rw [weightedConditionalVariances_eq_eventIntegrals
        distribution value center remaining (fun candidate member =>
          positive candidate (List.mem_cons_of_mem event member))]

/-- Exact finite law of total variance.  It decomposes dispersion into the
within-cell conditional variances and the between-cell squared shifts over a
displayed positive rational partition. -/
theorem total_variance {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalVariance event value +
            (distribution.conditionalMean event value -
              distribution.expectation value) ^ 2)).sum =
      distribution.variance value := by
  rw [weightedConditionalVariances_eq_eventIntegrals distribution value
    (distribution.expectation value) partition.events partition.positive]
  change
    (partition.toEventPartition.events.map fun event =>
      distribution.eventIntegral event
        (fun item => (value item - distribution.expectation value) ^ 2)).sum =
      distribution.expectation
        (fun item => (value item - distribution.expectation value) ^ 2)
  exact partition.toEventPartition.total_expectation
    (fun item => (value item - distribution.expectation value) ^ 2)

private theorem conditionalExpectation_varianceTerms
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event => distribution.probability event *
        (distribution.conditionalVariance event
            (partition.conditionalExpectation value) +
          (distribution.conditionalMean event
              (partition.conditionalExpectation value) -
            distribution.expectation
              (partition.conditionalExpectation value)) ^ 2)).sum =
      (events.map fun event => distribution.probability event *
        (distribution.conditionalMean event value -
          distribution.expectation value) ^ 2).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [partition.conditionalVariance_conditionalExpectation_eq_zero
          value event (subset event List.mem_cons_self),
        partition.conditionalMean_conditionalExpectation value event
          (subset event List.mem_cons_self),
        conditionalExpectation_varianceTerms partition value remaining
          (fun candidate member =>
            subset candidate (List.mem_cons_of_mem event member)),
        partition.expectation_conditionalExpectation value]
      ring1

/-- Variance of finite conditional expectation is exactly the displayed
between-cell variance. -/
theorem variance_conditionalExpectation_eq_between {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    distribution.variance (partition.conditionalExpectation value) =
      (partition.events.map fun event =>
        distribution.probability event *
          (distribution.conditionalMean event value -
            distribution.expectation value) ^ 2).sum := by
  calc
    distribution.variance (partition.conditionalExpectation value) =
        (partition.events.map fun event =>
          distribution.probability event *
            (distribution.conditionalVariance event
                (partition.conditionalExpectation value) +
              (distribution.conditionalMean event
                  (partition.conditionalExpectation value) -
                distribution.expectation
                  (partition.conditionalExpectation value)) ^ 2)).sum :=
      (partition.total_variance
        (partition.conditionalExpectation value)).symm
    _ = (partition.events.map fun event =>
          distribution.probability event *
            (distribution.conditionalMean event value -
              distribution.expectation value) ^ 2).sum :=
      conditionalExpectation_varianceTerms partition value partition.events
        (fun event member => member)

private theorem betweenVariance_le_totalVariance
    {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events →
        0 < distribution.probability event) →
      (events.map fun event => distribution.probability event *
        (distribution.conditionalMean event value -
          distribution.expectation value) ^ 2).sum ≤
      (events.map fun event => distribution.probability event *
        (distribution.conditionalVariance event value +
          (distribution.conditionalMean event value -
            distribution.expectation value) ^ 2)).sum
  | [], positive => le_rfl
  | event :: remaining, positive => by
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add
      · apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        · exact le_add_of_nonneg_left
            (distribution.conditionalVariance_nonneg event
              (positive event List.mem_cons_self) value)
        · exact distribution.probability_nonneg event
      · exact betweenVariance_le_totalVariance distribution value remaining
          (fun candidate member =>
            positive candidate (List.mem_cons_of_mem event member))

/-- Finite conditional expectation cannot increase variance. -/
theorem variance_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    distribution.variance (partition.conditionalExpectation value) ≤
      distribution.variance value := by
  rw [partition.variance_conditionalExpectation_eq_between value,
    ← partition.total_variance value]
  exact betweenVariance_le_totalVariance distribution value partition.events
    partition.positive

end PositiveEventPartition

end FiniteMeasure
