import FiniteMeasure.Coupling
import FiniteMeasure.DistributionEquivalence

/-!
# Coupling witnesses between named finite laws

A raw coupling computes its own marginals.  A `LawCoupling` additionally
certifies that those marginals agree in every exact evaluation with two
particular displayed distributions.  Thus transport estimates can be stated
directly about the named finite laws without quotienting atom tables.
-/

namespace FiniteMeasure

/-- One displayed joint table whose computed marginals evaluate exactly as
the two named finite distributions. -/
structure LawCoupling {α β : Type}
    (left : Distribution α) (right : Distribution β) where
  coupling : Coupling α β
  leftEquivalent : Distribution.EvaluationEquivalent
    coupling.leftMarginal left
  rightEquivalent : Distribution.EvaluationEquivalent
    coupling.rightMarginal right

namespace LawCoupling

/-- The graph joint table couples a finite law to its exact pushforward. -/
def graph {α β : Type} (source : Distribution α) (function : α → β) :
    LawCoupling source (source.map function) where
  coupling := Coupling.graph source function
  leftEquivalent := by
    constructor
    · exact Coupling.graph_leftMarginal_probability source function
    · exact Coupling.graph_leftMarginal_expectation source function
  rightEquivalent := by
    constructor
    · exact Coupling.graph_rightMarginal_probability source function
    · exact Coupling.graph_rightMarginal_expectation source function

/-- Couple two deterministic pushforwards of the same finite source by
retaining their common source row. -/
def ofMaps {α β γ : Type} (source : Distribution α)
    (left : α → β) (right : α → γ) :
    LawCoupling (source.map left) (source.map right) where
  coupling :=
    { joint := source.map fun item => (left item, right item) }
  leftEquivalent := by
    change Distribution.EvaluationEquivalent
      ((source.map fun item => (left item, right item)).map fun pair => pair.1)
      (source.map left)
    simpa only [] using source.map_map_evaluationEquivalent
      (fun item => (left item, right item)) (fun pair => pair.1)
  rightEquivalent := by
    change Distribution.EvaluationEquivalent
      ((source.map fun item => (left item, right item)).map fun pair => pair.2)
      (source.map right)
    simpa only [] using source.map_map_evaluationEquivalent
      (fun item => (left item, right item)) (fun pair => pair.2)

/-- Diagonal finite coupling of a named law with itself. -/
def refl {α : Type} (source : Distribution α) : LawCoupling source source := by
  let graphWitness := graph source (fun item => item)
  exact
    { coupling := graphWitness.coupling
      leftEquivalent := graphWitness.leftEquivalent
      rightEquivalent := graphWitness.rightEquivalent.trans
        (source.map_id_evaluationEquivalent) }

/-- Executable equality relation when the payload equality procedure is
supplied constructively. -/
def equalityRelation {α : Type} [DecidableEq α] (left right : α) : Bool :=
  decide (left = right)

/-- Couple every displayed source atom to one named deterministic target. -/
def collapse {α β : Type} (source : Distribution α) (target : β) :
    LawCoupling source (Distribution.pure target) := by
  let graphWitness := graph source (fun _ => target)
  exact
    { coupling := graphWitness.coupling
      leftEquivalent := graphWitness.leftEquivalent
      rightEquivalent := graphWitness.rightEquivalent.trans
        (source.map_const_evaluationEquivalent target) }

/-- Reverse a named-law coupling by explicitly swapping every joint row. -/
def symm {α β : Type} {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) : LawCoupling right left where
  coupling := witness.coupling.swap
  leftEquivalent :=
    { probability_eq := fun event =>
        (witness.coupling.swap_leftMarginal_probability event).trans
          (witness.rightEquivalent.probability_eq event)
      expectation_eq := fun value =>
        (witness.coupling.swap_leftMarginal_expectation value).trans
          (witness.rightEquivalent.expectation_eq value) }
  rightEquivalent :=
    { probability_eq := fun event =>
        (witness.coupling.swap_rightMarginal_probability event).trans
          (witness.leftEquivalent.probability_eq event)
      expectation_eq := fun value =>
        (witness.coupling.swap_rightMarginal_expectation value).trans
          (witness.leftEquivalent.expectation_eq value) }

/-- Exact mismatch mass of the displayed joint witness. -/
def mismatchProbability {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool) :
    Coordinate :=
  witness.coupling.mismatchProbability relation

theorem refl_mismatchProbability_eq_zero {α : Type} [DecidableEq α]
    (source : Distribution α) :
    (refl source).mismatchProbability equalityRelation = 0 := by
  unfold refl mismatchProbability
  change (Coupling.graph source (fun item => item)).mismatchProbability
    equalityRelation = 0
  apply Coupling.graph_mismatchProbability_eq_zero
  intro atom member
  unfold equalityRelation
  simp only [decide_true]

/-- Exact transport cost of the displayed joint witness. -/
def transportCost {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right)
    (cost : α → β → Coordinate) : Coordinate :=
  witness.coupling.transportCost cost

theorem mismatchProbability_nonneg {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool) :
    0 ≤ witness.mismatchProbability relation :=
  witness.coupling.mismatchProbability_nonneg relation

theorem mismatchProbability_le_one {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool) :
    witness.mismatchProbability relation ≤ 1 :=
  witness.coupling.mismatchProbability_le_one relation

/-- A displayed pointwise transport envelope controls expectation differences
between the two named finite laws. -/
theorem expectation_close_of_transportCost {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (cost : α → β → Coordinate)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate)
    (bounded : ∀ atom, atom ∈ witness.coupling.joint.atoms →
      rightValue atom.item.2 - leftValue atom.item.1 ≤
          cost atom.item.1 atom.item.2 ∧
        leftValue atom.item.1 - rightValue atom.item.2 ≤
          cost atom.item.1 atom.item.2) :
    right.expectation rightValue - left.expectation leftValue ≤
          witness.transportCost cost ∧
      left.expectation leftValue - right.expectation rightValue ≤
          witness.transportCost cost := by
  have estimate := witness.coupling.expectation_close_of_transportCost
    cost leftValue rightValue bounded
  rw [witness.leftEquivalent.expectation_eq leftValue,
    witness.rightEquivalent.expectation_eq rightValue] at estimate
  exact estimate

/-- Finite coupling inequality stated directly for the two named laws. -/
theorem probability_close_of_eventsAgree {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool)
    (leftEvent : α → Bool) (rightEvent : β → Bool)
    (agree : witness.coupling.EventsAgreeOn
      relation leftEvent rightEvent) :
    right.probability rightEvent - left.probability leftEvent ≤
          witness.mismatchProbability relation ∧
      left.probability leftEvent - right.probability rightEvent ≤
          witness.mismatchProbability relation := by
  have estimate := witness.coupling.probability_close_of_eventsAgree
    relation leftEvent rightEvent agree
  rw [witness.leftEquivalent.probability_eq leftEvent,
    witness.rightEquivalent.probability_eq rightEvent] at estimate
  exact estimate

end LawCoupling

end FiniteMeasure
