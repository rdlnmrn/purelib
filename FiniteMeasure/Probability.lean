import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Integration

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace FiniteMeasure

/-- A displayed finite rational probability distribution. -/
structure Distribution (α : Type) where
  atoms : List (Weighted α)
  total_one : totalWeight atoms = 1

namespace Distribution

/-- Two finite distributions with the same displayed weighted rows are
equal.  Their normalization fields are proofs and hence carry no additional
data. -/
theorem eq_of_atoms_eq {α : Type} (left right : Distribution α)
    (atomsEqual : left.atoms = right.atoms) : left = right := by
  cases left with
  | mk leftAtoms leftTotal =>
      cases right with
      | mk rightAtoms rightTotal =>
          cases atomsEqual
          rfl

end Distribution

/-- Exact weight selected by a finite Boolean event. -/
def eventWeight {α : Type} :
    List (Weighted α) → (α → Bool) → Coordinate
  | [], _ => 0
  | atom :: remaining, event =>
      (match event atom.item with
        | true => atom.weight
        | false => 0) +
        eventWeight remaining event

/-- Pointwise-equal finite events select the same exact weight. -/
theorem eventWeight_congr {α : Type}
    (atoms : List (Weighted α)) (left right : α → Bool)
    (pointwise : ∀ item, left item = right item) :
    eventWeight atoms left = eventWeight atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [eventWeight, pointwise atom.item, inductionHypothesis]

theorem eventWeight_nonneg {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool),
      0 ≤ eventWeight atoms event
  | [], _ => le_rfl
  | atom :: remaining, event => by
      cases choice : event atom.item
      · simpa only [eventWeight, choice, zero_add] using
          eventWeight_nonneg remaining event
      · simpa only [eventWeight, choice] using
          add_nonneg atom.nonnegative
            (eventWeight_nonneg remaining event)

theorem eventWeight_le_totalWeight {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool),
      eventWeight atoms event ≤ totalWeight atoms
  | [], _ => le_rfl
  | atom :: remaining, event => by
      cases choice : event atom.item
      · simp only [eventWeight, choice, zero_add, totalWeight]
        exact (eventWeight_le_totalWeight remaining event).trans
          (le_add_of_nonneg_left atom.nonnegative)
      · simp only [eventWeight, choice, totalWeight]
        exact add_le_add le_rfl
          (eventWeight_le_totalWeight remaining event)

/-- Boolean complement of a finite event. -/
def complementEvent {α : Type} (event : α → Bool) : α → Bool :=
  fun item => !(event item)

theorem eventWeight_add_complement {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool),
      eventWeight atoms event + eventWeight atoms (complementEvent event) =
        totalWeight atoms
  | [], _ => by
      simp only [eventWeight, totalWeight, add_zero]
  | atom :: remaining, event => by
      have inductionHypothesis := eventWeight_add_complement remaining event
      cases choice : event atom.item
      · simp only [eventWeight, choice, complementEvent, Bool.not_false,
          totalWeight]
        calc
          0 + eventWeight remaining event +
                (atom.weight + eventWeight remaining (complementEvent event)) =
              atom.weight +
                (eventWeight remaining event +
                  eventWeight remaining (complementEvent event)) := by ring1
          _ = atom.weight + totalWeight remaining :=
            congrArg (fun value => atom.weight + value) inductionHypothesis
      · simp only [eventWeight, choice, complementEvent, Bool.not_true,
          totalWeight]
        calc
          atom.weight + eventWeight remaining event +
                (0 + eventWeight remaining (complementEvent event)) =
              atom.weight +
                (eventWeight remaining event +
                  eventWeight remaining (complementEvent event)) := by ring1
          _ = atom.weight + totalWeight remaining :=
            congrArg (fun value => atom.weight + value) inductionHypothesis

/-- Boolean union of two finite events. -/
def unionEvent {α : Type} (first second : α → Bool) : α → Bool :=
  fun item => first item || second item

/-- Boolean intersection of two finite events. -/
def intersectionEvent {α : Type} (first second : α → Bool) : α → Bool :=
  fun item => first item && second item

/-- The exact finite valuation identity, valid without a disjointness
hypothesis. -/
theorem eventWeight_valuation {α : Type} :
    ∀ (atoms : List (Weighted α)) (first second : α → Bool),
      eventWeight atoms first + eventWeight atoms second =
        eventWeight atoms (unionEvent first second) +
          eventWeight atoms (intersectionEvent first second)
  | [], _, _ => by
      simp only [eventWeight, add_zero]
  | atom :: remaining, first, second => by
      have inductionHypothesis := eventWeight_valuation remaining first second
      let selected : (α → Bool) → Coordinate := fun event =>
        match event atom.item with
        | true => atom.weight
        | false => 0
      have headIdentity : selected first + selected second =
          selected (unionEvent first second) +
            selected (intersectionEvent first second) := by
        cases firstChoice : first atom.item
        · cases secondChoice : second atom.item
          · simp only [selected, unionEvent, intersectionEvent, firstChoice,
              secondChoice, Bool.false_or, Bool.false_and]
          · simp only [selected, unionEvent, intersectionEvent, firstChoice,
              secondChoice, Bool.false_or, Bool.false_and]
            ring1
        · cases secondChoice : second atom.item
          · simp only [selected, unionEvent, intersectionEvent, firstChoice,
              secondChoice, Bool.true_or, Bool.true_and]
          · simp only [selected, unionEvent, intersectionEvent, firstChoice,
              secondChoice, Bool.true_or, Bool.true_and]
      change
        selected first + eventWeight remaining first +
            (selected second + eventWeight remaining second) =
          selected (unionEvent first second) +
              eventWeight remaining (unionEvent first second) +
            (selected (intersectionEvent first second) +
              eventWeight remaining (intersectionEvent first second))
      calc
        selected first + eventWeight remaining first +
              (selected second + eventWeight remaining second) =
            (selected first + selected second) +
              (eventWeight remaining first + eventWeight remaining second) :=
          by ring1
        _ = (selected (unionEvent first second) +
                selected (intersectionEvent first second)) +
              (eventWeight remaining (unionEvent first second) +
                eventWeight remaining (intersectionEvent first second)) := by
          rw [headIdentity, inductionHypothesis]
        _ = selected (unionEvent first second) +
              eventWeight remaining (unionEvent first second) +
            (selected (intersectionEvent first second) +
              eventWeight remaining (intersectionEvent first second)) := by
          ring1

/-- Two Boolean events are disjoint on every displayed atom. -/
def DisjointOn {α : Type} (atoms : List (Weighted α))
    (first second : α → Bool) : Prop :=
  ∀ atom, atom ∈ atoms → ¬(first atom.item = true ∧ second atom.item = true)

/-- Pointwise finite event implication on the displayed atoms. -/
def EventImpliesOn {α : Type} (atoms : List (Weighted α))
    (first second : α → Bool) : Prop :=
  ∀ atom, atom ∈ atoms → first atom.item = true → second atom.item = true

theorem eventWeight_mono {α : Type} :
    ∀ {atoms : List (Weighted α)} {first second : α → Bool},
      EventImpliesOn atoms first second →
      eventWeight atoms first ≤ eventWeight atoms second
  | [], first, second, implication => le_rfl
  | atom :: remaining, first, second, implication => by
      have tail : EventImpliesOn remaining first second :=
        fun candidate member =>
          implication candidate (List.mem_cons_of_mem atom member)
      have inductionHypothesis := eventWeight_mono tail
      cases firstChoice : first atom.item
      · cases secondChoice : second atom.item
        · simpa only [eventWeight, firstChoice, secondChoice, zero_add] using
            inductionHypothesis
        · simp only [eventWeight, firstChoice, secondChoice, zero_add]
          exact inductionHypothesis.trans
            (le_add_of_nonneg_left atom.nonnegative)
      · have secondTrue := implication atom List.mem_cons_self firstChoice
        simp only [eventWeight, firstChoice, secondTrue]
        exact add_le_add le_rfl inductionHypothesis

theorem eventWeight_intersection_le_right {α : Type}
    (atoms : List (Weighted α)) (first second : α → Bool) :
    eventWeight atoms (intersectionEvent first second) ≤
      eventWeight atoms second := by
  apply eventWeight_mono
  intro atom member intersectionTrue
  cases firstChoice : first atom.item
  · simp only [intersectionEvent, firstChoice, Bool.false_and] at intersectionTrue
    cases intersectionTrue
  · cases secondChoice : second atom.item
    · simp only [intersectionEvent, firstChoice, secondChoice,
        Bool.true_and] at intersectionTrue
      cases intersectionTrue
    · exact rfl

theorem eventWeight_union_of_disjoint {α : Type} :
    ∀ {atoms : List (Weighted α)} {first second : α → Bool},
      DisjointOn atoms first second →
      eventWeight atoms (unionEvent first second) =
        eventWeight atoms first + eventWeight atoms second
  | [], first, second, disjoint => by
      simp only [eventWeight, add_zero]
  | atom :: remaining, first, second, disjoint => by
      have head := disjoint atom List.mem_cons_self
      have tail : DisjointOn remaining first second :=
        fun candidate member =>
          disjoint candidate (List.mem_cons_of_mem atom member)
      have inductionHypothesis := eventWeight_union_of_disjoint tail
      cases firstChoice : first atom.item
      · cases secondChoice : second atom.item
        · simp only [eventWeight, unionEvent, firstChoice, secondChoice,
            Bool.false_or, zero_add]
          exact inductionHypothesis
        · simp only [eventWeight, unionEvent, firstChoice, secondChoice,
            Bool.false_or]
          rw [inductionHypothesis]
          ring1
      · cases secondChoice : second atom.item
        · simp only [eventWeight, unionEvent, firstChoice, secondChoice,
            Bool.true_or]
          rw [inductionHypothesis]
          ring1
        · exact (head ⟨firstChoice, secondChoice⟩).elim

/-- Disjoint executable events have exactly zero intersection weight. -/
theorem eventWeight_intersection_eq_zero_of_disjoint {α : Type} :
    ∀ {atoms : List (Weighted α)} {first second : α → Bool},
      DisjointOn atoms first second →
      eventWeight atoms (intersectionEvent first second) = 0
  | [], first, second, disjoint => rfl
  | atom :: remaining, first, second, disjoint => by
      have head := disjoint atom List.mem_cons_self
      have tail : DisjointOn remaining first second :=
        fun candidate member =>
          disjoint candidate (List.mem_cons_of_mem atom member)
      have inductionHypothesis :=
        eventWeight_intersection_eq_zero_of_disjoint tail
      cases firstChoice : first atom.item
      · simp only [eventWeight, intersectionEvent, firstChoice,
          Bool.false_and, zero_add, inductionHypothesis]
      · cases secondChoice : second atom.item
        · simp only [eventWeight, intersectionEvent, firstChoice,
            secondChoice, Bool.and_false, zero_add, inductionHypothesis]
        · exact (head ⟨firstChoice, secondChoice⟩).elim

namespace Distribution

/-- Exact rational probability of a decidable finite event. -/
def probability {α : Type} (distribution : Distribution α)
    (event : α → Bool) : Coordinate :=
  eventWeight distribution.atoms event

/-- Pointwise-equal finite events have the same probability. -/
theorem probability_congr {α : Type} (distribution : Distribution α)
    (left right : α → Bool) (pointwise : ∀ item, left item = right item) :
    distribution.probability left = distribution.probability right :=
  eventWeight_congr distribution.atoms left right pointwise

theorem probability_nonneg {α : Type} (distribution : Distribution α)
    (event : α → Bool) : 0 ≤ distribution.probability event :=
  eventWeight_nonneg distribution.atoms event

theorem probability_le_one {α : Type} (distribution : Distribution α)
    (event : α → Bool) : distribution.probability event ≤ 1 := by
  rw [← distribution.total_one]
  exact eventWeight_le_totalWeight distribution.atoms event

theorem probability_add_complement {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    distribution.probability event +
      distribution.probability (complementEvent event) = 1 := by
  unfold probability
  rw [eventWeight_add_complement, distribution.total_one]

theorem probability_valuation {α : Type}
    (distribution : Distribution α) (first second : α → Bool) :
    distribution.probability first + distribution.probability second =
      distribution.probability (unionEvent first second) +
        distribution.probability (intersectionEvent first second) :=
  eventWeight_valuation distribution.atoms first second

/-- Exact finite additivity for disjoint displayed events. -/
theorem probability_union_of_disjoint {α : Type}
    (distribution : Distribution α) {first second : α → Bool}
    (disjoint : DisjointOn distribution.atoms first second) :
    distribution.probability (unionEvent first second) =
      distribution.probability first + distribution.probability second :=
  eventWeight_union_of_disjoint disjoint

/-- Exact zero probability of an explicitly disjoint intersection. -/
theorem probability_intersection_eq_zero_of_disjoint {α : Type}
    (distribution : Distribution α) {first second : α → Bool}
    (disjoint : DisjointOn distribution.atoms first second) :
    distribution.probability (intersectionEvent first second) = 0 :=
  eventWeight_intersection_eq_zero_of_disjoint disjoint

/-- Exact rational conditional probability with an explicit positive
conditioning-event certificate. -/
def conditionalProbability {α : Type} (distribution : Distribution α)
    (event condition : α → Bool)
    (_positive : 0 < distribution.probability condition) : Coordinate :=
  distribution.probability (intersectionEvent event condition) /
    distribution.probability condition

theorem conditionalProbability_nonneg {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    0 ≤ distribution.conditionalProbability event condition positive := by
  apply RFAP.ConstructiveFraction.div_nonneg_direct
  · exact distribution.probability_nonneg _
  · exact positive.le

theorem conditionalProbability_le_one {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.conditionalProbability event condition positive ≤ 1 := by
  apply (RFAP.ConstructiveFraction.div_le_iff_pos positive).2
  rw [one_mul]
  exact eventWeight_intersection_le_right distribution.atoms event condition

@[simp] theorem probability_false {α : Type}
    (distribution : Distribution α) :
    distribution.probability (fun _ => false) = 0 := by
  unfold probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [eventWeight, zero_add, inductionHypothesis]

@[simp] theorem probability_true {α : Type}
    (distribution : Distribution α) :
    distribution.probability (fun _ => true) = 1 := by
  unfold probability
  have allWeight : eventWeight distribution.atoms (fun _ => true) =
      totalWeight distribution.atoms := by
    induction distribution.atoms with
    | nil => rfl
    | cons atom remaining inductionHypothesis =>
        simp only [eventWeight, totalWeight,
          inductionHypothesis]
  rw [allWeight, distribution.total_one]

/-- Exact finite weighted evaluation used by expectation. -/
def expectationWeight {α : Type} :
    List (Weighted α) → (α → Coordinate) → Coordinate
  | [], _ => 0
  | atom :: remaining, value =>
      atom.weight * value atom.item + expectationWeight remaining value

/-- Pointwise-equal displayed observables have the same finite weighted
evaluation.  Keeping the hypothesis pointwise avoids identifying functions. -/
theorem expectationWeight_congr {α : Type}
    (atoms : List (Weighted α)) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    expectationWeight atoms left = expectationWeight atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, pointwise atom.item,
        inductionHypothesis]

theorem expectationWeight_add {α : Type}
    (atoms : List (Weighted α)) (left right : α → Coordinate) :
    expectationWeight atoms (fun item => left item + right item) =
      expectationWeight atoms left + expectationWeight atoms right := by
  induction atoms with
  | nil =>
      simp only [expectationWeight, add_zero]
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, inductionHypothesis]
      ring1

theorem expectationWeight_scale {α : Type}
    (atoms : List (Weighted α)) (factor : Coordinate)
    (value : α → Coordinate) :
    expectationWeight atoms (fun item => factor * value item) =
      factor * expectationWeight atoms value := by
  induction atoms with
  | nil =>
      simp only [expectationWeight, mul_zero]
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, inductionHypothesis]
      ring1

theorem expectationWeight_nonneg {α : Type}
    (atoms : List (Weighted α)) (value : α → Coordinate)
    (nonnegative : ∀ atom, atom ∈ atoms → 0 ≤ value atom.item) :
    0 ≤ expectationWeight atoms value := by
  induction atoms with
  | nil => exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have head := nonnegative atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          0 ≤ value candidate.item :=
        fun candidate member =>
          nonnegative candidate (List.mem_cons_of_mem atom member)
      exact add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct atom.nonnegative head)
        (inductionHypothesis tail)

theorem expectationWeight_mono {α : Type}
    (atoms : List (Weighted α)) (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ atoms →
      lower atom.item ≤ upper atom.item) :
    expectationWeight atoms lower ≤ expectationWeight atoms upper := by
  induction atoms with
  | nil => exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have head := pointwise atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          lower candidate.item ≤ upper candidate.item :=
        fun candidate member =>
          pointwise candidate (List.mem_cons_of_mem atom member)
      exact add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          head atom.nonnegative)
        (inductionHypothesis tail)

/-- A selected event's threshold-weight is bounded by a nonnegative finite
evaluation.  This is the list calculation underlying finite Markov
inequality. -/
theorem threshold_mul_eventWeight_le_expectationWeight {α : Type}
    (atoms : List (Weighted α)) (event : α → Bool)
    (value : α → Coordinate) (threshold : Coordinate)
    (nonnegative : ∀ atom, atom ∈ atoms → 0 ≤ value atom.item)
    (selectedLower : ∀ atom, atom ∈ atoms → event atom.item = true →
      threshold ≤ value atom.item) :
    threshold * eventWeight atoms event ≤
      expectationWeight atoms value := by
  induction atoms with
  | nil =>
      simp only [eventWeight, expectationWeight, mul_zero]
      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have headNonnegative := nonnegative atom List.mem_cons_self
      have tailNonnegative : ∀ candidate, candidate ∈ remaining →
          0 ≤ value candidate.item :=
        fun candidate member =>
          nonnegative candidate (List.mem_cons_of_mem atom member)
      have tailLower : ∀ candidate, candidate ∈ remaining →
          event candidate.item = true → threshold ≤ value candidate.item :=
        fun candidate member =>
          selectedLower candidate (List.mem_cons_of_mem atom member)
      have tailBound := inductionHypothesis tailNonnegative tailLower
      cases selected : event atom.item
      · simp only [eventWeight, selected, zero_add, expectationWeight]
        exact tailBound.trans
          (le_add_of_nonneg_left
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              atom.nonnegative headNonnegative))
      · have headLower :=
          selectedLower atom List.mem_cons_self selected
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            headLower atom.nonnegative
        simp only [eventWeight, selected, expectationWeight]
        calc
          threshold * (atom.weight + eventWeight remaining event) =
              atom.weight * threshold +
                threshold * eventWeight remaining event := by ring1
          _ ≤ atom.weight * value atom.item +
                expectationWeight remaining value :=
            add_le_add scaled tailBound

/-- Exact finite expectation of a displayed rational observable. -/
def expectation {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : Coordinate :=
  expectationWeight distribution.atoms value

/-- Pointwise equality is sufficient for equality of finite expectations. -/
theorem expectation_congr {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    distribution.expectation left = distribution.expectation right :=
  expectationWeight_congr distribution.atoms left right pointwise

theorem expectation_add {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.expectation (fun item => left item + right item) =
      distribution.expectation left + distribution.expectation right :=
  expectationWeight_add distribution.atoms left right

theorem expectation_scale {α : Type} (distribution : Distribution α)
    (factor : Coordinate) (value : α → Coordinate) :
    distribution.expectation (fun item => factor * value item) =
      factor * distribution.expectation value :=
  expectationWeight_scale distribution.atoms factor value

theorem expectation_nonneg {α : Type} (distribution : Distribution α)
    (value : α → Coordinate)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    0 ≤ distribution.expectation value :=
  expectationWeight_nonneg distribution.atoms value nonnegative

theorem expectation_mono {α : Type} (distribution : Distribution α)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      lower atom.item ≤ upper atom.item) :
    distribution.expectation lower ≤ distribution.expectation upper :=
  expectationWeight_mono distribution.atoms lower upper pointwise

/-- Constructive finite Markov inequality for an explicitly selected event.
The caller supplies finite certificates that the observable is nonnegative
and at least the positive threshold on every selected displayed atom. -/
theorem markov_bound {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Coordinate)
    (threshold : Coordinate) (positive : 0 < threshold)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (selectedLower : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true → threshold ≤ value atom.item) :
    distribution.probability event ≤
      distribution.expectation value / threshold := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos positive).2
  have bounded := threshold_mul_eventWeight_le_expectationWeight
    distribution.atoms event value threshold nonnegative selectedLower
  change eventWeight distribution.atoms event * threshold ≤
    expectationWeight distribution.atoms value
  calc
    eventWeight distribution.atoms event * threshold =
        threshold * eventWeight distribution.atoms event := by ring1
    _ ≤ expectationWeight distribution.atoms value := bounded

/-- Rational indicator of a finite Boolean event. -/
def indicator {α : Type} (event : α → Bool) (item : α) : Coordinate :=
  match event item with
  | true => 1
  | false => 0

theorem expectation_indicator {α : Type} (distribution : Distribution α)
    (event : α → Bool) :
    distribution.expectation (indicator event) =
      distribution.probability event := by
  unfold expectation probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases choice : event atom.item
      · simp only [expectationWeight, eventWeight, indicator, choice,
          mul_zero, zero_add, inductionHypothesis]
      · simp only [expectationWeight, eventWeight, indicator, choice,
          mul_one, inductionHypothesis]

private theorem weighted_constant {α : Type}
    (atoms : List (Weighted α)) (constant : Coordinate) :
    expectationWeight atoms (fun _ => constant) =
      totalWeight atoms * constant := by
  induction atoms with
  | nil =>
      simp only [expectationWeight, totalWeight, zero_mul]
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, totalWeight, inductionHypothesis]
      ring1

theorem expectation_constant {α : Type} (distribution : Distribution α)
    (constant : Coordinate) :
    distribution.expectation (fun _ => constant) = constant := by
  unfold expectation
  rw [weighted_constant, distribution.total_one, one_mul]

/-! ## Expectation as an exact finite integral -/

/-- Turn every probability atom into an exact integration cell for a
displayed rational observable. -/
def expectationCells {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : List (IntegrationCell α) :=
  distribution.atoms.map fun atom =>
    IntegrationCell.exact atom.item atom.weight (value atom.item)
      atom.nonnegative

theorem lowerIntegral_expectationCells {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    lowerIntegral (distribution.expectationCells value) =
      distribution.expectation value := by
  unfold expectationCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, lowerIntegral, expectationWeight]
      rw [inductionHypothesis]
      rfl

theorem upperIntegral_expectationCells {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    upperIntegral (distribution.expectationCells value) =
      distribution.expectation value := by
  unfold expectationCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, upperIntegral, expectationWeight]
      rw [inductionHypothesis]
      rfl

/-- A finite probability expectation is exactly a zero-width integral
enclosure. -/
theorem integralBound_expectationCells {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    integralBound (distribution.expectationCells value) =
      Bound.exact (distribution.expectation value) := by
  apply Bound.ext
  · exact distribution.lowerIntegral_expectationCells value
  · exact distribution.upperIntegral_expectationCells value

theorem integralBound_expectationCells_width {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    (integralBound (distribution.expectationCells value)).width = 0 := by
  rw [distribution.integralBound_expectationCells, Bound.exact_width]

/-! ## Exact finite dispersion -/

/-- Exact finite squared dispersion around a displayed rational center. -/
def varianceAround {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) (center : Coordinate) : Coordinate :=
  distribution.expectation (fun item => (value item - center) ^ 2)

/-- Pointwise-equal observables have the same squared dispersion around a
fixed displayed center. -/
theorem varianceAround_congr {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) (center : Coordinate)
    (pointwise : ∀ item, left item = right item) :
    distribution.varianceAround left center =
      distribution.varianceAround right center := by
  unfold varianceAround
  exact distribution.expectation_congr _ _ (fun item =>
    congrArg (fun value => (value - center) ^ 2) (pointwise item))

/-- Exact finite variance around the displayed rational expectation. -/
def variance {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : Coordinate :=
  distribution.varianceAround value (distribution.expectation value)

/-- Pointwise-equal observables have the same exact finite variance. -/
theorem variance_congr {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    distribution.variance left = distribution.variance right := by
  have meanEqual := distribution.expectation_congr left right pointwise
  unfold variance
  rw [meanEqual]
  exact distribution.varianceAround_congr left right
    (distribution.expectation right) pointwise

theorem varianceAround_nonneg {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) (center : Coordinate) :
    0 ≤ distribution.varianceAround value center := by
  apply distribution.expectation_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.sq_nonneg_direct
    (value atom.item - center)

theorem variance_nonneg {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : 0 ≤ distribution.variance value :=
  distribution.varianceAround_nonneg value (distribution.expectation value)

/-- Constructive finite Chebyshev inequality for an explicitly supplied
deviation event. -/
theorem chebyshev_bound {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Coordinate)
    (threshold : Coordinate) (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ^ 2 ≤
          (value atom.item - distribution.expectation value) ^ 2) :
    distribution.probability event ≤
      distribution.variance value / threshold ^ 2 := by
  apply distribution.markov_bound event
    (fun item => (value item - distribution.expectation value) ^ 2)
    (threshold ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2)
  · intro atom member
    exact RFAP.ConstructiveFraction.sq_nonneg_direct
      (value atom.item - distribution.expectation value)
  · exact selectedDeviation

/-- Classify every atom exactly with no unresolved mass. -/
def classifyEvent {α : Type} :
    List (Weighted α) → (α → Bool) → List (Classified α)
  | [], _ => []
  | atom :: remaining, event =>
      { atom := atom
        status := match event atom.item with
          | true => .inside
          | false => .outside } :: classifyEvent remaining event

def eventFrontier {α : Type} (distribution : Distribution α)
    (event : α → Bool) : List (Classified α) :=
  classifyEvent distribution.atoms event

theorem eventFrontier_unresolved_zero {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    unresolvedWeight (distribution.eventFrontier event) = 0 := by
  unfold eventFrontier
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases choice : event atom.item <;>
        simp only [classifyEvent, choice, unresolvedWeight, zero_add,
          inductionHypothesis]

theorem eventFrontier_bound_exact {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    (eventBound (distribution.eventFrontier event)).width = 0 := by
  rw [eventBound_width, distribution.eventFrontier_unresolved_zero]

end Distribution

end FiniteMeasure
