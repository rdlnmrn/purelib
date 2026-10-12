module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Stability
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Explicit finite couplings

A coupling here is one displayed finite rational distribution of pairs.  Its
two marginals are computed pushforwards, rather than separately postulated
measures.  A supplied executable relation identifies the pairs regarded as
matching.  The probability of its Boolean complement is then an exact finite
error budget for comparing marginal events and observables.

This is deliberately quantitative and finite: there is no limiting sequence,
completed sample space, or appeal to existence of an optimal coupling.
-/

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a finite joint distribution on two payload types.

Both marginals are obtained from this exact weighted occurrence list by coordinate projection; no marginal laws are
supplied separately. -/
structure Coupling (α β : Type) where
  /-- The exact finite joint distribution whose occurrences and weights determine both marginals. -/ joint :
    Distribution (α × β)

constructive_injectivity Coupling

namespace Coupling

/-- Pair each retained source occurrence with its exact image under the supplied function. -/
def graph {α β : Type} (source : Distribution α) (function : α → β) :
    Coupling α β where
  joint := source.map fun item => (item, function item)

/-- Swap coordinates of the exact retained joint distribution. -/
def swap {α β : Type} (coupling : Coupling α β) : Coupling β α where
  joint := coupling.joint.map fun pair => (pair.2, pair.1)

/-- Project the retained joint occurrences and weights onto their left payloads. -/
def leftMarginal {α β : Type} (coupling : Coupling α β) : Distribution α :=
  coupling.joint.map fun pair => pair.1

/-- Project the retained joint occurrences and weights onto their right payloads. -/
def rightMarginal {α β : Type} (coupling : Coupling α β) : Distribution β :=
  coupling.joint.map fun pair => pair.2

/-- Select exactly those payload pairs rejected by the supplied Boolean relation. -/
def mismatchEvent {α β : Type} (relation : α → β → Bool) :
    α × β → Bool :=
  fun pair => !(relation pair.1 pair.2)

open Purelib.Data.Rat in
/-- Measure the supplied relation's rejection event in the retained joint distribution. -/
def mismatchProbability {α β : Type} (coupling : Coupling α β)
    (relation : α → β → Bool) : Fraction.Rational :=
  coupling.joint.probability (mismatchEvent relation)

/-- Swapping the joint coordinates transposes the relation used to measure mismatch. -/
theorem swap_mismatchProbability {α β : Type}
    (coupling : Coupling α β) (relation : β → α → Bool) :
    coupling.swap.mismatchProbability relation =
      coupling.mismatchProbability (fun left right => relation right left) := by
  unfold mismatchProbability swap
  rw [coupling.joint.map_probability]
  rfl

/-- A left marginal event has the joint probability of its left-coordinate pullback. -/
theorem leftMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : α → Bool) :
    coupling.leftMarginal.probability event =
      coupling.joint.probability (fun pair => event pair.1) :=
  coupling.joint.map_probability (fun pair => pair.1) event

/-- A right marginal event has the joint probability of its right-coordinate pullback. -/
theorem rightMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : β → Bool) :
    coupling.rightMarginal.probability event =
      coupling.joint.probability (fun pair => event pair.2) :=
  coupling.joint.map_probability (fun pair => pair.2) event

section
open Purelib.Data.Rat
/-- A left marginal expectation equals the joint expectation of its left-coordinate pullback. -/
theorem leftMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : α → Fraction.Rational) :
    coupling.leftMarginal.expectation value =
      coupling.joint.expectation (fun pair => value pair.1) :=
  coupling.joint.map_expectation (fun pair => pair.1) value

/-- A right marginal expectation equals the joint expectation of its right-coordinate pullback. -/
theorem rightMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : β → Fraction.Rational) :
    coupling.rightMarginal.expectation value =
      coupling.joint.expectation (fun pair => value pair.2) :=
  coupling.joint.map_expectation (fun pair => pair.2) value

end

/-- The swapped left marginal has the original right marginal's event probabilities. -/
theorem swap_leftMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : β → Bool) :
    coupling.swap.leftMarginal.probability event =
      coupling.rightMarginal.probability event := by
  rw [leftMarginal_probability, swap,
    coupling.joint.map_probability, rightMarginal_probability]

/-- The swapped right marginal has the original left marginal's event probabilities. -/
theorem swap_rightMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : α → Bool) :
    coupling.swap.rightMarginal.probability event =
      coupling.leftMarginal.probability event := by
  rw [rightMarginal_probability, swap,
    coupling.joint.map_probability, leftMarginal_probability]

section
open Purelib.Data.Rat
/-- The swapped left marginal has the original right marginal's expectations. -/
theorem swap_leftMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : β → Fraction.Rational) :
    coupling.swap.leftMarginal.expectation value =
      coupling.rightMarginal.expectation value := by
  rw [leftMarginal_expectation, swap,
    coupling.joint.map_expectation, rightMarginal_expectation]

/-- The swapped right marginal has the original left marginal's expectations. -/
theorem swap_rightMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : α → Fraction.Rational) :
    coupling.swap.rightMarginal.expectation value =
      coupling.leftMarginal.expectation value := by
  rw [rightMarginal_expectation, swap,
    coupling.joint.map_expectation, leftMarginal_expectation]

end

/-- The graph coupling's left marginal retains the original source event probabilities. -/
theorem graph_leftMarginal_probability {α β : Type}
    (source : Distribution α) (function : α → β) (event : α → Bool) :
    (graph source function).leftMarginal.probability event =
      source.probability event := by
  rw [leftMarginal_probability, graph, source.map_probability]

/-- The graph coupling's right marginal has the probabilities of the exact source pushforward. -/
theorem graph_rightMarginal_probability {α β : Type}
    (source : Distribution α) (function : α → β) (event : β → Bool) :
    (graph source function).rightMarginal.probability event =
      (source.map function).probability event := by
  rw [rightMarginal_probability, graph, source.map_probability,
    source.map_probability]

section
open Purelib.Data.Rat
/-- The graph coupling's left marginal retains the original source expectations. -/
theorem graph_leftMarginal_expectation {α β : Type}
    (source : Distribution α) (function : α → β)
    (value : α → Fraction.Rational) :
    (graph source function).leftMarginal.expectation value =
      source.expectation value := by
  rw [leftMarginal_expectation, graph, source.map_expectation]

/-- The graph coupling's right marginal has the expectations of the exact source pushforward. -/
theorem graph_rightMarginal_expectation {α β : Type}
    (source : Distribution α) (function : α → β)
    (value : β → Fraction.Rational) :
    (graph source function).rightMarginal.expectation value =
      (source.map function).expectation value := by
  rw [rightMarginal_expectation, graph, source.map_expectation,
    source.map_expectation]

end

/-- A relation holding on every retained source occurrence and its image has zero mismatch under the graph coupling. -/
theorem graph_mismatchProbability_eq_zero {α β : Type}
    (source : Distribution α) (function : α → β)
    (relation : α → β → Bool)
    (related : ∀ atom, atom ∈ source.atoms →
      relation atom.item (function atom.item) = true) :
    (graph source function).mismatchProbability relation = 0 := by
  unfold mismatchProbability
  rw [graph, source.map_probability]
  change eventWeight source.atoms
      (fun item => !(relation item (function item))) = 0
  have zeroWeight : ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        relation atom.item (function atom.item) = true) →
      eventWeight atoms
          (fun item => !(relation item (function item))) = 0 := by
    intro atoms
    induction atoms with
    | nil => intro _; rfl
    | cons atom remaining inductionHypothesis =>
        intro certified
        have head := certified atom List.mem_cons_self
        have tail : ∀ candidate, candidate ∈ remaining →
            relation candidate.item (function candidate.item) = true :=
          fun candidate member =>
            certified candidate (List.mem_cons_of_mem atom member)
        simp only [eventWeight, head, Bool.not_true, zero_add]
        exact inductionHypothesis tail
  exact zeroWeight source.atoms related

section
open Purelib.Data.Rat
/-- Integrate the supplied pair cost over the exact retained joint distribution. -/
def transportCost {α β : Type} (coupling : Coupling α β)
    (cost : α → β → Fraction.Rational) : Fraction.Rational :=
  coupling.joint.expectation fun pair => cost pair.1 pair.2

/-- Swapping joint coordinates transposes the pair cost in the transport integral. -/
theorem swap_transportCost {α β : Type} (coupling : Coupling α β)
    (cost : β → α → Fraction.Rational) :
    coupling.swap.transportCost cost =
      coupling.transportCost (fun left right => cost right left) := by
  unfold transportCost swap
  rw [coupling.joint.map_expectation]

/-- A cost nonnegative on every retained joint occurrence has nonnegative transport integral. -/
theorem transportCost_nonneg {α β : Type} (coupling : Coupling α β)
    (cost : α → β → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ coupling.joint.atoms →
      0 ≤ cost atom.item.1 atom.item.2) :
    0 ≤ coupling.transportCost cost :=
  coupling.joint.expectation_nonneg _ nonnegative

/-- A pair cost bounding both signed observable differences bounds both signed marginal expectation differences.

The bound is required only on the original joint occurrences; integrating it retains the exact coupling and its original
weights. -/
theorem expectation_close_of_transportCost {α β : Type}
    (coupling : Coupling α β) (cost : α → β → Fraction.Rational)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational)
    (bounded : ∀ atom, atom ∈ coupling.joint.atoms →
      rightValue atom.item.2 - leftValue atom.item.1 ≤
          cost atom.item.1 atom.item.2 ∧
        leftValue atom.item.1 - rightValue atom.item.2 ≤
          cost atom.item.1 atom.item.2) :
    coupling.rightMarginal.expectation rightValue -
          coupling.leftMarginal.expectation leftValue ≤
        coupling.transportCost cost ∧
      coupling.leftMarginal.expectation leftValue -
          coupling.rightMarginal.expectation rightValue ≤
        coupling.transportCost cost := by
  have bound := coupling.joint.expectation_symmetricError
    (fun pair => cost pair.1 pair.2)
    (fun pair => leftValue pair.1) (fun pair => rightValue pair.2)
    bounded
  rw [← coupling.leftMarginal_expectation leftValue,
    ← coupling.rightMarginal_expectation rightValue] at bound
  exact bound

/-- Bound both marginal expectation differences by ordinary error plus extra error times mismatch probability.

Related retained pairs satisfy the ordinary error bound; rejected pairs satisfy ordinary plus extra error, with both
signed differences certified separately. -/
theorem expectation_close_of_relation {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool)
    (ordinary extra : Fraction.Rational)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational)
    (related : ∀ atom, atom ∈ coupling.joint.atoms →
      relation atom.item.1 atom.item.2 = true →
        rightValue atom.item.2 - leftValue atom.item.1 ≤ ordinary ∧
          leftValue atom.item.1 - rightValue atom.item.2 ≤ ordinary)
    (mismatched : ∀ atom, atom ∈ coupling.joint.atoms →
      mismatchEvent relation atom.item = true →
        rightValue atom.item.2 - leftValue atom.item.1 ≤ ordinary + extra ∧
          leftValue atom.item.1 - rightValue atom.item.2 ≤ ordinary + extra) :
    coupling.rightMarginal.expectation rightValue -
          coupling.leftMarginal.expectation leftValue ≤
        ordinary + extra * coupling.mismatchProbability relation ∧
      coupling.leftMarginal.expectation leftValue -
          coupling.rightMarginal.expectation rightValue ≤
        ordinary + extra * coupling.mismatchProbability relation := by
  have outside : ∀ atom, atom ∈ coupling.joint.atoms →
      mismatchEvent relation atom.item = false →
        rightValue atom.item.2 - leftValue atom.item.1 ≤ ordinary ∧
          leftValue atom.item.1 - rightValue atom.item.2 ≤ ordinary := by
    intro atom member notMismatch
    cases relationValue : relation atom.item.1 atom.item.2
    · simp only [mismatchEvent, relationValue, Bool.not_false] at notMismatch
      cases notMismatch
    · exact related atom member relationValue
  have bound := coupling.joint.expectation_close_outside_event
    (mismatchEvent relation) ordinary extra
    (fun pair => leftValue pair.1) (fun pair => rightValue pair.2)
    outside mismatched
  rw [← coupling.leftMarginal_expectation leftValue,
    ← coupling.rightMarginal_expectation rightValue] at bound
  exact bound

end

/-- Require the two Boolean events to agree on all related retained joint occurrences. -/
def EventsAgreeOn {α β : Type} (coupling : Coupling α β)
    (relation : α → β → Bool)
    (leftEvent : α → Bool) (rightEvent : β → Bool) : Prop :=
  ∀ atom, atom ∈ coupling.joint.atoms →
    relation atom.item.1 atom.item.2 = true →
      leftEvent atom.item.1 = rightEvent atom.item.2

/-- Events agreeing on related retained pairs have probability differences bounded in both directions by mismatch
probability. -/
theorem probability_close_of_eventsAgree {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool)
    (leftEvent : α → Bool) (rightEvent : β → Bool)
    (agree : coupling.EventsAgreeOn relation leftEvent rightEvent) :
    coupling.rightMarginal.probability rightEvent -
          coupling.leftMarginal.probability leftEvent ≤
        coupling.mismatchProbability relation ∧
      coupling.leftMarginal.probability leftEvent -
          coupling.rightMarginal.probability rightEvent ≤
        coupling.mismatchProbability relation := by
  have related : ∀ atom, atom ∈ coupling.joint.atoms →
      relation atom.item.1 atom.item.2 = true →
        Distribution.indicator rightEvent atom.item.2 -
              Distribution.indicator leftEvent atom.item.1 ≤ 0 ∧
          Distribution.indicator leftEvent atom.item.1 -
              Distribution.indicator rightEvent atom.item.2 ≤ 0 := by
    intro atom member relationTrue
    have same := agree atom member relationTrue
    unfold Distribution.indicator
    rw [← same, sub_self]
    exact ⟨le_rfl, le_rfl⟩
  have mismatched : ∀ atom, atom ∈ coupling.joint.atoms →
      mismatchEvent relation atom.item = true →
        Distribution.indicator rightEvent atom.item.2 -
              Distribution.indicator leftEvent atom.item.1 ≤ 0 + 1 ∧
          Distribution.indicator leftEvent atom.item.1 -
              Distribution.indicator rightEvent atom.item.2 ≤ 0 + 1 := by
    intro atom member mismatch
    cases leftSelected : leftEvent atom.item.1 <;>
      cases rightSelected : rightEvent atom.item.2 <;>
      simp only [Distribution.indicator, leftSelected, rightSelected,
        zero_add] <;>
      decide
  have bound := coupling.expectation_close_of_relation relation 0 1
    (Distribution.indicator leftEvent) (Distribution.indicator rightEvent)
    related mismatched
  rw [coupling.leftMarginal.expectation_indicator,
    coupling.rightMarginal.expectation_indicator,
    zero_add, one_mul] at bound
  exact bound

/-- The retained joint distribution gives every mismatch event nonnegative probability. -/
theorem mismatchProbability_nonneg {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool) :
    0 ≤ coupling.mismatchProbability relation :=
  coupling.joint.probability_nonneg (mismatchEvent relation)

/-- Every retained mismatch probability is at most one. -/
theorem mismatchProbability_le_one {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool) :
    coupling.mismatchProbability relation ≤ 1 :=
  coupling.joint.probability_le_one (mismatchEvent relation)

end Coupling

end Purelib.Measure
