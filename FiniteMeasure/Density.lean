import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ContentIntegral

/-!
# Finite rational change of measure

A rational density reweights a displayed finite atom list by multiplication.
The resulting change-of-measure identities are exact finite sums.  There is
no almost-everywhere quotient, measurable function space, or Radon--Nikodym
existence theorem.
-/

namespace FiniteMeasure

/-- Multiply each displayed atom by a globally nonnegative rational density. -/
def densityAtoms {α : Type} (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) :
    List (Weighted α) → List (Weighted α)
  | [] => []
  | atom :: remaining =>
      { item := atom.item
        weight := atom.weight * density atom.item
        nonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
          atom.nonnegative (nonnegative atom.item) } ::
        densityAtoms density nonnegative remaining

theorem densityAtoms_length {α : Type} (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) :
    ∀ atoms : List (Weighted α),
      (densityAtoms density nonnegative atoms).length = atoms.length
  | [] => rfl
  | atom :: remaining => by
      simp only [densityAtoms, List.length_cons,
        densityAtoms_length density nonnegative remaining]

/-- Total reweighted mass is the original finite evaluation of the density. -/
theorem totalWeight_densityAtoms {α : Type}
    (atoms : List (Weighted α)) (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) :
    totalWeight (densityAtoms density nonnegative atoms) =
      Distribution.expectationWeight atoms density := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [densityAtoms, totalWeight, Distribution.expectationWeight,
        inductionHypothesis]

/-- Reweighted expectation is multiplication by the density inside the
original finite sum. -/
theorem expectationWeight_densityAtoms {α : Type}
    (atoms : List (Weighted α)) (density value : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) :
    Distribution.expectationWeight
        (densityAtoms density nonnegative atoms) value =
      Distribution.expectationWeight atoms
        (fun item => density item * value item) := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [densityAtoms, Distribution.expectationWeight,
        inductionHypothesis]
      ring1

/-- Reweighted event content is the original expectation of density times
the rational event indicator. -/
theorem eventWeight_densityAtoms {α : Type}
    (atoms : List (Weighted α)) (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) (event : α → Bool) :
    eventWeight (densityAtoms density nonnegative atoms) event =
      Distribution.expectationWeight atoms
        (fun item => density item * Distribution.indicator event item) := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item <;>
        simp only [densityAtoms, eventWeight, Distribution.expectationWeight,
          Distribution.indicator, selected, mul_zero, mul_one, zero_add,
          inductionHypothesis]

/-- A displayed upper bound on density gives finite absolute-continuity
control on every executable event. -/
theorem eventWeight_densityAtoms_le {α : Type}
    (atoms : List (Weighted α)) (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) (ceiling : Coordinate)
    (bounded : ∀ atom, atom ∈ atoms → density atom.item ≤ ceiling)
    (event : α → Bool) :
    eventWeight (densityAtoms density nonnegative atoms) event ≤
      ceiling * eventWeight atoms event := by
  induction atoms with
  | nil =>
      simp only [densityAtoms, eventWeight, mul_zero]
      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have head := bounded atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          density candidate.item ≤ ceiling :=
        fun candidate member =>
          bounded candidate (List.mem_cons_of_mem atom member)
      have tailBound := inductionHypothesis tail
      cases selected : event atom.item
      · simp only [densityAtoms, eventWeight, selected, zero_add]
        exact tailBound
      · have headScaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            head atom.nonnegative
        simp only [densityAtoms, eventWeight, selected]
        calc
          atom.weight * density atom.item +
                eventWeight (densityAtoms density nonnegative remaining) event ≤
              atom.weight * ceiling +
                ceiling * eventWeight remaining event :=
            add_le_add headScaled tailBound
          _ = ceiling * (atom.weight + eventWeight remaining event) := by ring1

/-- A zero-weight event remains zero after any displayed nonnegative density
change.  Finiteness makes a separate bounded-density hypothesis unnecessary:
each selected source atom is forced to have weight zero. -/
theorem eventWeight_densityAtoms_eq_zero_of_eventWeight_eq_zero
    {α : Type} (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) (event : α → Bool) :
    ∀ atoms : List (Weighted α), eventWeight atoms event = 0 →
      eventWeight (densityAtoms density nonnegative atoms) event = 0
  | [], zero => rfl
  | atom :: remaining, zero => by
      cases selected : event atom.item
      · simp only [densityAtoms, eventWeight, selected, zero_add] at zero ⊢
        exact eventWeight_densityAtoms_eq_zero_of_eventWeight_eq_zero
          density nonnegative event remaining zero
      · have eventZero :
            atom.weight + eventWeight remaining event = 0 := by
          simpa only [eventWeight, selected] using zero
        have tailNonnegative := eventWeight_nonneg remaining event
        have atomZero : atom.weight = 0 := by
          apply RFAP.ConstructiveFraction.le_antisymm
          · calc
              atom.weight ≤ atom.weight + eventWeight remaining event :=
                le_add_of_nonneg_right tailNonnegative
              _ = 0 := eventZero
          · exact atom.nonnegative
        have tailZero : eventWeight remaining event = 0 := by
          apply RFAP.ConstructiveFraction.le_antisymm
          · calc
              eventWeight remaining event ≤
                  atom.weight + eventWeight remaining event :=
                le_add_of_nonneg_left atom.nonnegative
              _ = 0 := eventZero
          · exact tailNonnegative
        simp only [densityAtoms, eventWeight, selected, atomZero, zero_mul,
          zero_add]
        exact eventWeight_densityAtoms_eq_zero_of_eventWeight_eq_zero
          density nonnegative event remaining tailZero

namespace FiniteContent

/-- Reweight a displayed finite content by a nonnegative rational density. -/
def reweight {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item) :
    FiniteContent α :=
  ⟨densityAtoms density nonnegative content.atoms⟩

theorem reweight_total {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item) :
    (content.reweight density nonnegative).total =
      Distribution.expectationWeight content.atoms density :=
  totalWeight_densityAtoms content.atoms density nonnegative

theorem reweight_measure {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (event : α → Bool) :
    (content.reweight density nonnegative).measure event =
      Distribution.expectationWeight content.atoms
        (fun item => density item * Distribution.indicator event item) :=
  eventWeight_densityAtoms content.atoms density nonnegative event

/-- Exact finite change-of-density identity for arbitrary rational
observables. -/
theorem reweight_integral {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (value : α → Coordinate) :
    (content.reweight density nonnegative).integral value =
      content.integral (fun item => density item * value item) :=
  expectationWeight_densityAtoms content.atoms density value nonnegative

theorem reweight_measure_le {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (ceiling : Coordinate)
    (bounded : ∀ atom, atom ∈ content.atoms → density atom.item ≤ ceiling)
    (event : α → Bool) :
    (content.reweight density nonnegative).measure event ≤
      ceiling * content.measure event :=
  eventWeight_densityAtoms_le content.atoms density nonnegative ceiling
    bounded event

/-- A zero-content executable event stays zero after every displayed
nonnegative density change. -/
theorem reweight_measure_zero {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (event : α → Bool) (zero : content.measure event = 0) :
    (content.reweight density nonnegative).measure event = 0 :=
  eventWeight_densityAtoms_eq_zero_of_eventWeight_eq_zero density nonnegative
    event content.atoms zero

/-- Successive finite density changes multiply their rational densities
inside every exact integral. -/
theorem reweight_reweight_integral {α : Type}
    (content : FiniteContent α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (value : α → Coordinate) :
    ((content.reweight first firstNonnegative).reweight
        second secondNonnegative).integral value =
      (content.reweight (fun item => first item * second item)
        (fun item => RFAP.ConstructiveFraction.mul_nonneg_direct
          (firstNonnegative item) (secondNonnegative item))).integral value := by
  calc
    ((content.reweight first firstNonnegative).reweight
          second secondNonnegative).integral value =
        (content.reweight first firstNonnegative).integral
          (fun item => second item * value item) :=
      (content.reweight first firstNonnegative).reweight_integral
        second secondNonnegative value
    _ = content.integral
          (fun item => first item * (second item * value item)) :=
      content.reweight_integral first firstNonnegative
        (fun item => second item * value item)
    _ = content.integral
          (fun item => (first item * second item) * value item) := by
      exact content.integral_congr _ _ (fun item => by ring1)
    _ = (content.reweight (fun item => first item * second item)
          (fun item => RFAP.ConstructiveFraction.mul_nonneg_direct
            (firstNonnegative item) (secondNonnegative item))).integral value :=
      (content.reweight_integral (fun item => first item * second item)
        (fun item => RFAP.ConstructiveFraction.mul_nonneg_direct
          (firstNonnegative item) (secondNonnegative item)) value).symm

/-- The same finite density chain rule evaluated on an executable event. -/
theorem reweight_reweight_measure {α : Type}
    (content : FiniteContent α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (event : α → Bool) :
    ((content.reweight first firstNonnegative).reweight
        second secondNonnegative).measure event =
      (content.reweight (fun item => first item * second item)
        (fun item => RFAP.ConstructiveFraction.mul_nonneg_direct
          (firstNonnegative item) (secondNonnegative item))).measure event := by
  rw [← (content.reweight first firstNonnegative).reweight
      second secondNonnegative |>.integral_indicator event]
  rw [content.reweight_reweight_integral first second firstNonnegative
    secondNonnegative (Distribution.indicator event)]
  exact (content.reweight (fun item => first item * second item)
    (fun item => RFAP.ConstructiveFraction.mul_nonneg_direct
      (firstNonnegative item) (secondNonnegative item))).integral_indicator event

end FiniteContent

namespace Distribution

/-- Normalize-preserving finite rational change of probability. -/
def reweight {α : Type} (distribution : Distribution α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1) : Distribution α where
  atoms := densityAtoms density nonnegative distribution.atoms
  total_one := by
    rw [totalWeight_densityAtoms]
    exact normalizes

theorem reweight_probability {α : Type} (distribution : Distribution α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (event : α → Bool) :
    (distribution.reweight density nonnegative normalizes).probability event =
      distribution.expectation
        (fun item => density item * indicator event item) :=
  eventWeight_densityAtoms distribution.atoms density nonnegative event

theorem reweight_expectation {α : Type} (distribution : Distribution α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (value : α → Coordinate) :
    (distribution.reweight density nonnegative normalizes).expectation value =
      distribution.expectation
        (fun item => density item * value item) :=
  expectationWeight_densityAtoms distribution.atoms density value nonnegative

end Distribution

end FiniteMeasure
