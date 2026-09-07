import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Family
import FiniteMeasure.Cumulative
import FiniteMeasure.NaturalLp
import FiniteMeasure.SamplingRequest

/-!
# Simultaneous finite event-frequency sampling

One explicit finite iid sample can estimate every event probability in a
displayed finite event list.  The requested failure budget is split over
`events.length + 1`, each event uses the uniform Bernoulli variance bound, and
finite subadditivity controls the union of all deviation events.

This is the finite constructive core of a uniform empirical-frequency bound;
there is no infinite event class, supremum, or asymptotic empirical process.
-/

namespace FiniteMeasure

namespace Distribution

/-- Positive rational failure share assigned to each event in a displayed
finite family. -/
def eventFamilyFailureShare {α : Type}
    (events : List (α → Bool)) (failure : Coordinate) : Coordinate :=
  failure / (Nat.succ events.length : Coordinate)

/-- One shared sample count for all events in a displayed finite family. -/
def requiredEventFamilyFrequencySampleCount {α : Type}
    (events : List (α → Bool))
    (threshold failure : Coordinate) : Nat :=
  requiredEventFrequencySampleCount threshold
    (eventFamilyFailureShare events failure)

/-- Union of all event-frequency deviation events on one finite sample list. -/
def simultaneousEventFrequencyDeviation {α : Type}
    (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Coordinate) : List α → Bool :=
  unionEvents (events.map fun event =>
    eventFrequencyDeviation source count event threshold)

/-- Pointwise meaning of simultaneous finite event-frequency accuracy. -/
def EventFamilyFrequenciesAccurate {α : Type}
    (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Coordinate) (sample : List α) : Prop :=
  ∀ event, event ∈ events →
    (eventFrequency count event sample - source.probability event) ^ 2 <
      threshold ^ 2

/-- Ordinary rational-separation form of simultaneous event-frequency
accuracy. -/
def EventFamilyFrequenciesWithin {α : Type}
    (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Coordinate) (sample : List α) : Prop :=
  ∀ event, event ∈ events →
    rationalSeparation (eventFrequency count event sample)
      (source.probability event) < threshold

/-- Outside the single displayed deviation union, every event in the finite
family has squared frequency error strictly below the requested squared
tolerance. -/
theorem eventFamilyFrequenciesAccurate_of_outside
    {α : Type} (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Coordinate) (sample : List α)
    (outside : simultaneousEventFrequencyDeviation source events count
      threshold sample = false) :
    EventFamilyFrequenciesAccurate source events count threshold sample := by
  intro event member
  have deviationMember :
      eventFrequencyDeviation source count event threshold ∈
        events.map fun candidate =>
          eventFrequencyDeviation source count candidate threshold :=
    QuotientFreeList.mem_map.mpr ⟨event, member, rfl⟩
  have deviationFalse :
      eventFrequencyDeviation source count event threshold sample = false :=
    event_eq_false_of_mem_of_unionEvents_eq_false
      (events.map fun candidate =>
        eventFrequencyDeviation source count candidate threshold)
      (eventFrequencyDeviation source count event threshold)
      deviationMember sample outside
  have notLarge : ¬threshold ^ 2 ≤
      (eventFrequency count event sample - source.probability event) ^ 2 := by
    unfold eventFrequencyDeviation sampleMeanDeviation at deviationFalse
    have raw := decide_eq_false_iff_not.mp deviationFalse
    rw [source.expectation_indicator] at raw
    exact raw
  exact RFAP.ConstructiveFraction.lt_of_not_ge_direct notLarge

/-- With a positive supplied tolerance, being outside the single deviation
union means every displayed frequency is ordinarily within that tolerance
of its exact event probability. -/
theorem eventFamilyFrequenciesWithin_of_outside
    {α : Type} (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (sample : List α)
    (outside : simultaneousEventFrequencyDeviation source events count
      threshold sample = false) :
    EventFamilyFrequenciesWithin source events count threshold sample := by
  have squared := eventFamilyFrequenciesAccurate_of_outside source events
    count threshold sample outside
  intro event member
  apply rationalSeparation_lt_of_sq_lt_sq thresholdPositive
  rw [rationalSeparation_sq]
  exact squared event member

theorem eventFamilyFailureShare_positive {α : Type}
    (events : List (α → Bool)) {failure : Coordinate}
    (failurePositive : 0 < failure) :
    0 < eventFamilyFailureShare events failure :=
  RFAP.ConstructiveFraction.div_pos_direct failurePositive
    (RFAP.ConstructiveFraction.natCast_pos_direct (Nat.zero_lt_succ _))

theorem sum_map_le_length_mul_of_bounded {β : Type}
    (items : List β) (value : β → Coordinate) (ceiling : Coordinate)
    (bounded : ∀ item, item ∈ items → value item ≤ ceiling) :
    (items.map value).sum ≤ (items.length : Coordinate) * ceiling := by
  induction items with
  | nil =>
      simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero,
        zero_mul]
      exact le_rfl
  | cons item remaining inductionHypothesis =>
      have tailBounded : ∀ candidate, candidate ∈ remaining →
          value candidate ≤ ceiling := by
        intro candidate member
        exact bounded candidate (List.mem_cons_of_mem item member)
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        value item + (remaining.map value).sum ≤
            ceiling + (remaining.length : Coordinate) * ceiling :=
          RFAP.ConstructiveFraction.add_le_add_direct
            (bounded item List.mem_cons_self)
            (inductionHypothesis tailBounded)
        _ = ((remaining.length : Coordinate) + 1) * ceiling := by ring1

theorem length_mul_eventFamilyFailureShare_lt {α : Type}
    (events : List (α → Bool)) {failure : Coordinate}
    (failurePositive : 0 < failure) :
    (events.length : Coordinate) * eventFamilyFailureShare events failure <
      failure := by
  have denominatorPositive :
      0 < (Nat.succ events.length : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct (Nat.zero_lt_succ _)
  have castLess : (events.length : Coordinate) <
      (Nat.succ events.length : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct (Nat.lt_succ_self _)
  have scaledLess : failure * (events.length : Coordinate) <
      failure * (Nat.succ events.length : Coordinate) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      failurePositive castLess
  calc
    (events.length : Coordinate) * eventFamilyFailureShare events failure =
        (failure * (events.length : Coordinate)) /
          (Nat.succ events.length : Coordinate) := by
      unfold eventFamilyFailureShare
      calc
        (events.length : Coordinate) *
            (failure / (Nat.succ events.length : Coordinate)) =
          (events.length : Coordinate) *
            (failure * (Nat.succ events.length : Coordinate)⁻¹) := by
          rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        _ = ((events.length : Coordinate) * failure) *
            (Nat.succ events.length : Coordinate)⁻¹ :=
          (RFAP.ConstructiveFraction.mul_assoc
            (events.length : Coordinate) failure
            (Nat.succ events.length : Coordinate)⁻¹).symm
        _ = (failure * (events.length : Coordinate)) *
            (Nat.succ events.length : Coordinate)⁻¹ := by
          rw [RFAP.ConstructiveFraction.mul_comm
            (events.length : Coordinate) failure]
        _ = (failure * (events.length : Coordinate)) /
            (Nat.succ events.length : Coordinate) := by
          rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    _ < failure :=
      (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
        scaledLess

/-- The shared executable sample count makes the probability of *any*
displayed event-frequency error at least `threshold` strictly smaller than
the supplied positive rational family failure budget. -/
theorem iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
    {α : Type} (source : Distribution α)
    (events : List (α → Bool))
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredEventFamilyFrequencySampleCount
          events threshold failure)).probability
      (simultaneousEventFrequencyDeviation source events
        (requiredEventFamilyFrequencySampleCount events threshold failure)
        threshold) < failure := by
  let share := eventFamilyFailureShare events failure
  let count := requiredEventFamilyFrequencySampleCount events threshold failure
  let sampleLaw := source.iidSamples count
  let deviations : List (List α → Bool) := events.map fun event =>
    eventFrequencyDeviation source count event threshold
  have sharePositive : 0 < share :=
    eventFamilyFailureShare_positive events failurePositive
  calc
    sampleLaw.probability (unionEvents deviations) ≤
        (deviations.map sampleLaw.probability).sum :=
      sampleLaw.probability_unionEvents_le_sum deviations
    _ ≤ (events.length : Coordinate) * share := by
      change (((events.map fun event =>
          eventFrequencyDeviation source count event threshold).map
            sampleLaw.probability).sum ≤
        (events.length : Coordinate) * share)
      rw [List.map_map]
      apply sum_map_le_length_mul_of_bounded events
        (fun event => sampleLaw.probability
          (eventFrequencyDeviation source count event threshold)) share
      intro event member
      exact (source.iidSamples_eventFrequency_deviationProbability_lt_requested
        event threshold thresholdPositive share sharePositive).le
    _ < failure :=
      length_mul_eventFamilyFailureShare_lt events failurePositive

/-! ## Finite empirical cumulative grids -/

/-- Displayed finite family of lower-ray events for a rational threshold
grid. -/
def cumulativeEventGrid (thresholds : List Coordinate) :
    List (Coordinate → Bool) :=
  thresholds.map atMostEvent

/-- Shared sample count for uniformly estimating a displayed finite set of
cumulative probabilities. -/
def requiredCumulativeGridSampleCount
    (thresholds : List Coordinate)
    (tolerance failure : Coordinate) : Nat :=
  requiredEventFamilyFrequencySampleCount
    (cumulativeEventGrid thresholds) tolerance failure

/-- Union of all empirical cumulative-frequency deviations on a displayed
rational threshold grid. -/
def empiricalCumulativeGridDeviation
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate) : List Coordinate → Bool :=
  simultaneousEventFrequencyDeviation source
    (cumulativeEventGrid thresholds) count tolerance

/-- Pointwise meaning of an accurate empirical cumulative grid. -/
def EmpiricalCumulativeGridAccurate
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate)
    (sample : List Coordinate) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    (eventFrequency count (atMostEvent threshold) sample -
      source.cumulative threshold) ^ 2 < tolerance ^ 2

/-- Ordinary rational-separation form of empirical cumulative-grid
accuracy. -/
def EmpiricalCumulativeGridWithin
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate)
    (sample : List Coordinate) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    rationalSeparation
      (eventFrequency count (atMostEvent threshold) sample)
      (source.cumulative threshold) < tolerance

/-- Outside the one empirical-CDF deviation union, every threshold in the
displayed rational grid has squared frequency error below the requested
squared tolerance. -/
theorem empiricalCumulativeGridAccurate_of_outside
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate) (sample : List Coordinate)
    (outside : empiricalCumulativeGridDeviation source thresholds count
      tolerance sample = false) :
    EmpiricalCumulativeGridAccurate source thresholds count tolerance
      sample := by
  intro threshold member
  have eventMember : atMostEvent threshold ∈
      cumulativeEventGrid thresholds := by
    unfold cumulativeEventGrid
    exact QuotientFreeList.mem_map.mpr ⟨threshold, member, rfl⟩
  have accurate := eventFamilyFrequenciesAccurate_of_outside source
    (cumulativeEventGrid thresholds) count tolerance sample outside
  exact accurate (atMostEvent threshold) eventMember

/-- Outside the empirical-CDF deviation union, every displayed cumulative
frequency is ordinarily within the supplied positive rational tolerance. -/
theorem empiricalCumulativeGridWithin_of_outside
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (sample : List Coordinate)
    (outside : empiricalCumulativeGridDeviation source thresholds count
      tolerance sample = false) :
    EmpiricalCumulativeGridWithin source thresholds count tolerance sample := by
  intro threshold member
  have within := eventFamilyFrequenciesWithin_of_outside source
    (cumulativeEventGrid thresholds) count tolerance tolerancePositive sample
    outside
  exact within (atMostEvent threshold)
    (QuotientFreeList.mem_map.mpr ⟨threshold, member, rfl⟩)

/-- One executable finite iid request controls the empirical cumulative
frequency at every threshold in a displayed rational grid. -/
theorem iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalCumulativeGridDeviation source thresholds
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        tolerance) < failure :=
  source.iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
    (cumulativeEventGrid thresholds) tolerance tolerancePositive failure
    failurePositive

end Distribution

end FiniteMeasure
