module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Weighted.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Boolean events on finite weighted occurrence lists

Event weights scan an explicitly retained list of nonnegative rational
weights. Boolean complement, union, and intersection preserve the original
occurrences, and their weight identities require no normalization.
-/

namespace Purelib.Measure

section
open Purelib.Data.Rat
/-- Sum the weights of the exact retained occurrences selected by a Boolean event.

Selection reads each original payload. Repeated payloads retain their separate weights and the original list order;
unselected occurrences contribute zero. -/
@[expose] def eventWeight {α : Type} :
    List (Weighted α) → (α → Bool) → Fraction.Rational
  | [], _ => 0
  | atom :: remaining, event =>
      (match event atom.item with
        | true => atom.weight
        | false => 0) +
        eventWeight remaining event

/-- Pointwise equal Boolean events have equal weight on the same retained list.

At each retained occurrence, equality of the two Boolean tests identifies
its scalar contribution. Scalar congruence then transports the unchanged
recursive tail without identifying the event functions themselves. -/
theorem eventWeight_congr {α : Type}
    (atoms : List (Weighted α)) (left right : α → Bool)
    (pointwise : ∀ item, left item = right item) :
    eventWeight atoms left = eventWeight atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      let selected : Bool → Fraction.Rational := fun decision =>
        match decision with | true => atom.weight | false => 0
      change selected (left atom.item) + eventWeight remaining left =
        selected (right atom.item) + eventWeight remaining right
      exact (congrArg (fun head => head + eventWeight remaining left)
        (congrArg selected (pointwise atom.item))).trans
          (congrArg (fun tail => selected (right atom.item) + tail) ih)

end

/-- Every Boolean event has nonnegative weight on a finite nonnegative weighted list. -/
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

/-- Every event's selected weight is at most the same retained list's total weight. -/
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

/-- Negate the supplied Boolean event at each payload. -/
@[expose] def complementEvent {α : Type} (event : α → Bool) : α → Bool :=
  fun item => !(event item)

open Purelib.Data.Rat in
/-- An event and its Boolean complement partition the exact retained total weight.

The complementary head tests contribute the original weight exactly once.
Scalar regrouping and the same complement identity on the original tail
recover the retained total without changing any occurrence. -/
theorem eventWeight_add_complement {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool),
      eventWeight atoms event + eventWeight atoms (complementEvent event) =
        totalWeight atoms
  | [], _ => Fraction.Field.zero_add 0
  | atom :: remaining, event => by
      let selected : Bool → Fraction.Rational := fun decision =>
        match decision with | true => atom.weight | false => 0
      have head : selected (event atom.item) + selected (!(event atom.item)) =
          atom.weight := by
        cases event atom.item with
        | false => exact Fraction.Field.zero_add atom.weight
        | true =>
            exact (Fraction.Field.add_comm atom.weight 0).trans
              (Fraction.Field.zero_add atom.weight)
      change selected (event atom.item) + eventWeight remaining event +
          (selected (!(event atom.item)) +
            eventWeight remaining (complementEvent event)) =
        atom.weight + totalWeight remaining
      calc
        _ = (selected (event atom.item) + selected (!(event atom.item))) +
            (eventWeight remaining event +
              eventWeight remaining (complementEvent event)) := by ring1
        _ = atom.weight + (eventWeight remaining event +
              eventWeight remaining (complementEvent event)) :=
          congrArg (fun value => value + (eventWeight remaining event +
            eventWeight remaining (complementEvent event))) head
        _ = atom.weight + totalWeight remaining :=
          congrArg (fun tail => atom.weight + tail)
            (eventWeight_add_complement remaining event)

/-- Select a payload when either supplied Boolean event selects it. -/
@[expose] def unionEvent {α : Type} (first second : α → Bool) : α → Bool :=
  fun item => first item || second item

/-- Select a payload when both supplied Boolean events select it. -/
@[expose] def intersectionEvent {α : Type} (first second : α → Bool) : α → Bool :=
  fun item => first item && second item

open Purelib.Data.Rat in
/-- The sum of two event weights equals the weights of their union and intersection.

The four Boolean head cases satisfy the scalar valuation identity for the
same retained weight. Scalar regrouping combines that identity with the
valuation of the original recursive tail. -/
theorem eventWeight_valuation {α : Type} :
    ∀ (atoms : List (Weighted α)) (first second : α → Bool),
      eventWeight atoms first + eventWeight atoms second =
        eventWeight atoms (unionEvent first second) +
          eventWeight atoms (intersectionEvent first second)
  | [], _, _ => rfl
  | atom :: remaining, first, second => by
      let selected : Bool → Fraction.Rational := fun decision =>
        match decision with | true => atom.weight | false => 0
      have head : selected (first atom.item) + selected (second atom.item) =
          selected (first atom.item || second atom.item) +
            selected (first atom.item && second atom.item) := by
        cases first atom.item with
        | false =>
            cases second atom.item with
            | false => rfl
            | true => exact Fraction.Field.add_comm 0 atom.weight
        | true => cases second atom.item <;> rfl
      change selected (first atom.item) + eventWeight remaining first +
          (selected (second atom.item) + eventWeight remaining second) =
        selected (first atom.item || second atom.item) +
            eventWeight remaining (unionEvent first second) +
          (selected (first atom.item && second atom.item) +
            eventWeight remaining (intersectionEvent first second))
      calc
        _ = (selected (first atom.item) + selected (second atom.item)) +
            (eventWeight remaining first + eventWeight remaining second) := by ring1
        _ = (selected (first atom.item || second atom.item) +
              selected (first atom.item && second atom.item)) +
            (eventWeight remaining first + eventWeight remaining second) :=
          congrArg (fun value => value + (eventWeight remaining first +
            eventWeight remaining second)) head
        _ = (selected (first atom.item || second atom.item) +
              selected (first atom.item && second atom.item)) +
            (eventWeight remaining (unionEvent first second) +
              eventWeight remaining (intersectionEvent first second)) :=
          congrArg (fun tail => (selected (first atom.item || second atom.item) +
            selected (first atom.item && second atom.item)) + tail)
              (eventWeight_valuation remaining first second)
        _ = _ := by ring1

/-- Require the two Boolean events never to select the same retained occurrence. -/
@[expose] def DisjointOn {α : Type} (atoms : List (Weighted α))
    (first second : α → Bool) : Prop :=
  ∀ atom, atom ∈ atoms → ¬(first atom.item = true ∧ second atom.item = true)

/-- Require selection by the first event to imply selection by the second on every retained occurrence. -/
@[expose] def EventImpliesOn {α : Type} (atoms : List (Weighted α))
    (first second : α → Bool) : Prop :=
  ∀ atom, atom ∈ atoms → first atom.item = true → second atom.item = true

/-- Implication on the retained occurrences makes event weight monotone. -/
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

/-- The intersection's weight is at most the second event's weight on the same retained list. -/
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

open Purelib.Data.Rat
/-- Events disjoint on the retained occurrences have additive union weight.

Disjointness rules out simultaneous selection at the original head and
restricts directly to the original tail. The remaining Boolean cases and
scalar regrouping give the union sum with both event scans unchanged. -/
theorem eventWeight_union_of_disjoint {α : Type} :
    ∀ {atoms : List (Weighted α)} {first second : α → Bool},
      DisjointOn atoms first second →
      eventWeight atoms (unionEvent first second) =
        eventWeight atoms first + eventWeight atoms second
  | [], _, _, _ => (Fraction.Field.zero_add 0).symm
  | atom :: remaining, first, second, disjoint => by
      have headDisjoint := disjoint atom (List.Mem.head remaining)
      have tail : DisjointOn remaining first second :=
        fun candidate member => disjoint candidate (List.Mem.tail atom member)
      let selected : Bool → Fraction.Rational := fun decision =>
        match decision with | true => atom.weight | false => 0
      have head : selected (first atom.item || second atom.item) =
          selected (first atom.item) + selected (second atom.item) := by
        cases firstChoice : first atom.item with
        | false =>
            cases second atom.item with
            | false => exact (Fraction.Field.zero_add 0).symm
            | true => exact (Fraction.Field.zero_add atom.weight).symm
        | true =>
            cases secondChoice : second atom.item with
            | false => exact ((Fraction.Field.add_comm atom.weight 0).trans
                (Fraction.Field.zero_add atom.weight)).symm
            | true => exact (headDisjoint ⟨firstChoice, secondChoice⟩).elim
      change selected (first atom.item || second atom.item) +
          eventWeight remaining (unionEvent first second) =
        selected (first atom.item) + eventWeight remaining first +
          (selected (second atom.item) + eventWeight remaining second)
      calc
        _ = (selected (first atom.item) + selected (second atom.item)) +
            eventWeight remaining (unionEvent first second) :=
          congrArg (fun value => value +
            eventWeight remaining (unionEvent first second)) head
        _ = (selected (first atom.item) + selected (second atom.item)) +
            (eventWeight remaining first + eventWeight remaining second) :=
          congrArg (fun value =>
            (selected (first atom.item) + selected (second atom.item)) + value)
              (eventWeight_union_of_disjoint tail)
        _ = _ := by ring1

/-- Events disjoint on the retained occurrences have zero intersection weight.

The original disjointness witness makes the head intersection contribution
zero and restricts directly to the same tail. Scalar zero addition transports
the recursive zero weight without changing either Boolean event. -/
theorem eventWeight_intersection_eq_zero_of_disjoint {α : Type} :
    ∀ {atoms : List (Weighted α)} {first second : α → Bool},
      DisjointOn atoms first second →
      eventWeight atoms (intersectionEvent first second) = 0
  | [], _, _, _ => rfl
  | atom :: remaining, first, second, disjoint => by
      have headDisjoint := disjoint atom (List.Mem.head remaining)
      have tail : DisjointOn remaining first second :=
        fun candidate member => disjoint candidate (List.Mem.tail atom member)
      let selected : Bool → Fraction.Rational := fun decision =>
        match decision with | true => atom.weight | false => 0
      have head : selected (first atom.item && second atom.item) = 0 := by
        cases firstChoice : first atom.item with
        | false => rfl
        | true =>
            cases secondChoice : second atom.item with
            | false => rfl
            | true => exact (headDisjoint ⟨firstChoice, secondChoice⟩).elim
      change selected (first atom.item && second atom.item) +
        eventWeight remaining (intersectionEvent first second) = 0
      exact (congrArg (fun value => value +
        eventWeight remaining (intersectionEvent first second)) head).trans
          ((Fraction.Field.zero_add _).trans
            (eventWeight_intersection_eq_zero_of_disjoint tail))

end Purelib.Measure

end

section
@[expose] public section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

namespace Purelib.CCL.Measure.CylinderConcentration

open Purelib in
/-- An event false on every retained occurrence has weight zero. -/
public theorem eventWeight_eq_zero_of_false_on_atoms {ι : Type}
    (atoms : List (Measure.Weighted ι)) (event : ι → Bool)
    (falseOn : ∀ atom, atom ∈ atoms → event atom.item = false) :
    Measure.eventWeight atoms event = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have headFalse := falseOn atom List.mem_cons_self
      have tailFalse : ∀ candidate, candidate ∈ remaining →
          event candidate.item = false := by
        intro candidate member
        exact falseOn candidate (List.mem_cons_of_mem atom member)
      simp only [Measure.eventWeight, headFalse, zero_add]
      exact inductionHypothesis tailFalse

end Purelib.CCL.Measure.CylinderConcentration

end

section
@[expose] public section

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace Purelib.CCL.Measure.SquaredCylinderConcentration

open Purelib in
/-- An event false on every retained occurrence has weight zero. -/
public theorem eventWeight_eq_zero_of_false_on_atoms {index :
  Type}
    (atoms : List (Measure.Weighted index))
    (event : index → Bool)
    (falseOn : ∀ atom, atom ∈ atoms → event atom.item = false) :
    Measure.eventWeight atoms event = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have headFalse := falseOn atom List.mem_cons_self
      have tailFalse : ∀ candidate, candidate ∈ remaining →
          event candidate.item = false := by
        intro candidate member
        exact falseOn candidate (List.mem_cons_of_mem atom member)
      simp only [Measure.eventWeight, headFalse, zero_add]
      exact inductionHypothesis tailFalse

end Purelib.CCL.Measure.SquaredCylinderConcentration

end

section
/-!
# Exact finite absorption from a decreasing rank

An absorbing Boolean event and a displayed natural-valued rank give an exact
finite hitting theorem when every transition outside the event either enters
the event or strictly decreases the rank.  The proof follows atom-table
membership through finite binds.  It uses no limiting argument, infinite
path, compactness principle, or choice.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

/-- An event true on every retained occurrence has the exact total list weight. -/
public theorem eventWeight_eq_totalWeight_of_all {alpha : Type}
    (event : alpha → Bool) :
    ∀ atoms : List (Weighted alpha),
      (∀ atom, atom ∈ atoms → event atom.item = true) →
      eventWeight atoms event = totalWeight atoms
  | [], _ => rfl
  | atom :: remaining, selected => by
      simp only [eventWeight, selected atom List.mem_cons_self, totalWeight]
      rw [eventWeight_eq_totalWeight_of_all event remaining]
      intro target member
      exact selected target (List.mem_cons_of_mem atom member)

end Distribution

end Purelib.Measure

end
