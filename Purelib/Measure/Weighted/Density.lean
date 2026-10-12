module
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite rational change of measure

A rational density reweights a displayed finite atom list by multiplication.
The resulting change-of-measure identities are exact finite sums.  There is
no almost-everywhere quotient, measurable function space, or Radon--Nikodym
existence theorem.
-/

namespace Purelib.Measure

section
open Purelib.Data.Rat
/-- Multiply each exact occurrence weight by a pointwise nonnegative rational density.

Retain the original payload order and multiplicities. Every new weight carries the direct product-nonnegativity proof
for that same occurrence and density value. -/
def densityAtoms {α : Type} (density : α → Fraction.Rational)
    (nonnegative : ∀ item, 0 ≤ density item) :
    List (Weighted α) → List (Weighted α)
  | [] => []
  | atom :: remaining =>
      { item := atom.item
        weight := atom.weight * density atom.item
        nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
          atom.nonnegative (nonnegative atom.item) } ::
        densityAtoms density nonnegative remaining

/-- Density weighting preserves the exact occurrence count.

Every original weighted occurrence receives the supplied nonnegative density without adding or removing a payload. -/
theorem densityAtoms_length {α : Type} (density : α → Fraction.Rational)
    (nonnegative : ∀ item, 0 ≤ density item) :
    ∀ atoms : List (Weighted α),
      (densityAtoms density nonnegative atoms).length = atoms.length
  | [] => rfl
  | atom :: remaining => by
      simp only [densityAtoms, List.length_cons,
        densityAtoms_length density nonnegative remaining, -eq_self, -iff_self]
      rfl

/-- The density-weighted total equals the original finite integral of the density.

Each original weight is multiplied by its own payload density, retaining the same ordered finite sum. -/
theorem totalWeight_densityAtoms {α : Type}
    (atoms : List (Weighted α)) (density : α → Fraction.Rational)
    (nonnegative : ∀ item, 0 ≤ density item) :
    totalWeight (densityAtoms density nonnegative atoms) =
      Distribution.expectationWeight atoms density := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [densityAtoms, totalWeight, Distribution.expectationWeight,
        inductionHypothesis, -eq_self, -iff_self]
      rfl

/-- Integrating after density weighting equals integrating the pointwise density-observable product originally. -/
theorem expectationWeight_densityAtoms {α : Type}
    (atoms : List (Weighted α)) (density value : α → Fraction.Rational)
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

/-- The density-weighted event mass equals the original integral of density times its Boolean indicator.

Selection uses the original event on each retained payload, with zero contribution for every unselected occurrence. -/
theorem eventWeight_densityAtoms {α : Type}
    (atoms : List (Weighted α)) (density : α → Fraction.Rational)
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
          inductionHypothesis, -eq_self, -iff_self] <;> rfl

/-- A density bounded on retained occurrences bounds every new event weight by that ceiling times its original weight.
-/
theorem eventWeight_densityAtoms_le {α : Type}
    (atoms : List (Weighted α)) (density : α → Fraction.Rational)
    (nonnegative : ∀ item, 0 ≤ density item) (ceiling : Fraction.Rational)
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
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            head atom.nonnegative
        simp only [densityAtoms, eventWeight, selected]
        calc
          atom.weight * density atom.item +
                eventWeight (densityAtoms density nonnegative remaining) event ≤
              atom.weight * ceiling +
                ceiling * eventWeight remaining event :=
            add_le_add headScaled tailBound
          _ = ceiling * (atom.weight + eventWeight remaining event) := by ring1

/-- Pointwise nonnegative density weighting preserves every zero-weight Boolean event. -/
theorem eventWeight_densityAtoms_eq_zero_of_eventWeight_eq_zero
    {α : Type} (density : α → Fraction.Rational)
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
          apply Fraction.Order.Basic.Compatibility.le_antisymm
          · calc
              atom.weight ≤ atom.weight + eventWeight remaining event :=
                le_add_of_nonneg_right tailNonnegative
              _ = 0 := eventZero
          · exact atom.nonnegative
        have tailZero : eventWeight remaining event = 0 := by
          apply Fraction.Order.Basic.Compatibility.le_antisymm
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

end

namespace Content
end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
