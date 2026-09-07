import FiniteMeasure.Stability
import FiniteMeasure.Stochastic

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

namespace FiniteMeasure

/-- One explicit finite joint distribution, with its marginals obtained by
finite pushforward. -/
structure Coupling (α β : Type) where
  joint : Distribution (α × β)

namespace Coupling

/-- Graph coupling of one finite distribution with a displayed deterministic
map. -/
def graph {α β : Type} (source : Distribution α) (function : α → β) :
    Coupling α β where
  joint := source.map fun item => (item, function item)

/-- Swap both coordinates in every displayed joint-table row. -/
def swap {α β : Type} (coupling : Coupling α β) : Coupling β α where
  joint := coupling.joint.map fun pair => (pair.2, pair.1)

/-- The exact finite left marginal of a coupling. -/
def leftMarginal {α β : Type} (coupling : Coupling α β) : Distribution α :=
  coupling.joint.map fun pair => pair.1

/-- The exact finite right marginal of a coupling. -/
def rightMarginal {α β : Type} (coupling : Coupling α β) : Distribution β :=
  coupling.joint.map fun pair => pair.2

/-- The executable event of pairs not certified by a supplied relation. -/
def mismatchEvent {α β : Type} (relation : α → β → Bool) :
    α × β → Bool :=
  fun pair => !(relation pair.1 pair.2)

/-- Exact rational mass of the displayed mismatching pairs. -/
def mismatchProbability {α β : Type} (coupling : Coupling α β)
    (relation : α → β → Bool) : Coordinate :=
  coupling.joint.probability (mismatchEvent relation)

theorem swap_mismatchProbability {α β : Type}
    (coupling : Coupling α β) (relation : β → α → Bool) :
    coupling.swap.mismatchProbability relation =
      coupling.mismatchProbability (fun left right => relation right left) := by
  unfold mismatchProbability swap
  rw [coupling.joint.map_probability]
  rfl

theorem leftMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : α → Bool) :
    coupling.leftMarginal.probability event =
      coupling.joint.probability (fun pair => event pair.1) :=
  coupling.joint.map_probability (fun pair => pair.1) event

theorem rightMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : β → Bool) :
    coupling.rightMarginal.probability event =
      coupling.joint.probability (fun pair => event pair.2) :=
  coupling.joint.map_probability (fun pair => pair.2) event

theorem leftMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : α → Coordinate) :
    coupling.leftMarginal.expectation value =
      coupling.joint.expectation (fun pair => value pair.1) :=
  coupling.joint.map_expectation (fun pair => pair.1) value

theorem rightMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : β → Coordinate) :
    coupling.rightMarginal.expectation value =
      coupling.joint.expectation (fun pair => value pair.2) :=
  coupling.joint.map_expectation (fun pair => pair.2) value

theorem swap_leftMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : β → Bool) :
    coupling.swap.leftMarginal.probability event =
      coupling.rightMarginal.probability event := by
  rw [leftMarginal_probability, swap,
    coupling.joint.map_probability, rightMarginal_probability]

theorem swap_rightMarginal_probability {α β : Type}
    (coupling : Coupling α β) (event : α → Bool) :
    coupling.swap.rightMarginal.probability event =
      coupling.leftMarginal.probability event := by
  rw [rightMarginal_probability, swap,
    coupling.joint.map_probability, leftMarginal_probability]

theorem swap_leftMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : β → Coordinate) :
    coupling.swap.leftMarginal.expectation value =
      coupling.rightMarginal.expectation value := by
  rw [leftMarginal_expectation, swap,
    coupling.joint.map_expectation, rightMarginal_expectation]

theorem swap_rightMarginal_expectation {α β : Type}
    (coupling : Coupling α β) (value : α → Coordinate) :
    coupling.swap.rightMarginal.expectation value =
      coupling.leftMarginal.expectation value := by
  rw [rightMarginal_expectation, swap,
    coupling.joint.map_expectation, leftMarginal_expectation]

theorem graph_leftMarginal_probability {α β : Type}
    (source : Distribution α) (function : α → β) (event : α → Bool) :
    (graph source function).leftMarginal.probability event =
      source.probability event := by
  rw [leftMarginal_probability, graph, source.map_probability]

theorem graph_rightMarginal_probability {α β : Type}
    (source : Distribution α) (function : α → β) (event : β → Bool) :
    (graph source function).rightMarginal.probability event =
      (source.map function).probability event := by
  rw [rightMarginal_probability, graph, source.map_probability,
    source.map_probability]

theorem graph_leftMarginal_expectation {α β : Type}
    (source : Distribution α) (function : α → β)
    (value : α → Coordinate) :
    (graph source function).leftMarginal.expectation value =
      source.expectation value := by
  rw [leftMarginal_expectation, graph, source.map_expectation]

theorem graph_rightMarginal_expectation {α β : Type}
    (source : Distribution α) (function : α → β)
    (value : β → Coordinate) :
    (graph source function).rightMarginal.expectation value =
      (source.map function).expectation value := by
  rw [rightMarginal_expectation, graph, source.map_expectation,
    source.map_expectation]

/-- A relation certified on every displayed source atom gives zero mismatch
mass for its graph coupling. -/
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

/-- Exact finite expected transport cost of a displayed coupling. -/
def transportCost {α β : Type} (coupling : Coupling α β)
    (cost : α → β → Coordinate) : Coordinate :=
  coupling.joint.expectation fun pair => cost pair.1 pair.2

theorem swap_transportCost {α β : Type} (coupling : Coupling α β)
    (cost : β → α → Coordinate) :
    coupling.swap.transportCost cost =
      coupling.transportCost (fun left right => cost right left) := by
  unfold transportCost swap
  rw [coupling.joint.map_expectation]

theorem transportCost_nonneg {α β : Type} (coupling : Coupling α β)
    (cost : α → β → Coordinate)
    (nonnegative : ∀ atom, atom ∈ coupling.joint.atoms →
      0 ≤ cost atom.item.1 atom.item.2) :
    0 ≤ coupling.transportCost cost :=
  coupling.joint.expectation_nonneg _ nonnegative

/-- A pointwise cost envelope on the displayed joint table controls both
directed differences of marginal expectations. -/
theorem expectation_close_of_transportCost {α β : Type}
    (coupling : Coupling α β) (cost : α → β → Coordinate)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate)
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

/-- A relation certificate turns a two-level pointwise error allowance into
an exact marginal-expectation bound.  The ordinary allowance is charged on
every pair; the extra allowance is charged only to the displayed mismatch
probability. -/
theorem expectation_close_of_relation {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool)
    (ordinary extra : Coordinate)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate)
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

/-- Two marginal events agree on every pair certified by the relation. -/
def EventsAgreeOn {α β : Type} (coupling : Coupling α β)
    (relation : α → β → Bool)
    (leftEvent : α → Bool) (rightEvent : β → Bool) : Prop :=
  ∀ atom, atom ∈ coupling.joint.atoms →
    relation atom.item.1 atom.item.2 = true →
      leftEvent atom.item.1 = rightEvent atom.item.2

/-- Finite coupling inequality.  For any two executable events agreeing on
related displayed pairs, both directed differences of their exact marginal
probabilities are bounded by the rational mismatch mass. -/
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

theorem mismatchProbability_nonneg {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool) :
    0 ≤ coupling.mismatchProbability relation :=
  coupling.joint.probability_nonneg (mismatchEvent relation)

theorem mismatchProbability_le_one {α β : Type}
    (coupling : Coupling α β) (relation : α → β → Bool) :
    coupling.mismatchProbability relation ≤ 1 :=
  coupling.joint.probability_le_one (mismatchEvent relation)

end Coupling

end FiniteMeasure
