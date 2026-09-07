import FiniteMeasure.ContentIntegral
import FiniteMeasure.Consolidation

/-!
# Evaluation equivalence of finite contents

Finite contents retain their displayed atom-table layout.  Observational
equivalence records equality of every executable event measure and every
rational integral without quotienting those tables.  Consolidation and the
basic finite-content operations respect this relation.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- Constructive observational equality of two displayed finite contents. -/
structure EvaluationEquivalent {α : Type}
    (left right : FiniteContent α) : Prop where
  measure_eq : ∀ event : α → Bool,
    left.measure event = right.measure event
  integral_eq : ∀ value : α → Coordinate,
    left.integral value = right.integral value

namespace EvaluationEquivalent

/-- Equality of every rational integral already gives event-measure
equality, by testing indicator observables. -/
theorem of_integral_eq {α : Type} {left right : FiniteContent α}
    (integralEqual : ∀ value : α → Coordinate,
      left.integral value = right.integral value) :
    EvaluationEquivalent left right where
  measure_eq event := by
    rw [← left.integral_indicator event, ← right.integral_indicator event]
    exact integralEqual _
  integral_eq := integralEqual

theorem refl {α : Type} (content : FiniteContent α) :
    EvaluationEquivalent content content where
  measure_eq _ := rfl
  integral_eq _ := rfl

theorem symm {α : Type} {left right : FiniteContent α}
    (equivalent : EvaluationEquivalent left right) :
    EvaluationEquivalent right left where
  measure_eq event := (equivalent.measure_eq event).symm
  integral_eq value := (equivalent.integral_eq value).symm

theorem trans {α : Type} {first second third : FiniteContent α}
    (firstSecond : EvaluationEquivalent first second)
    (secondThird : EvaluationEquivalent second third) :
    EvaluationEquivalent first third where
  measure_eq event :=
    (firstSecond.measure_eq event).trans (secondThird.measure_eq event)
  integral_eq value :=
    (firstSecond.integral_eq value).trans (secondThird.integral_eq value)

/-- Appending equivalent content tables on each side preserves every exact
evaluation. -/
theorem append {α : Type}
    {leftFirst leftSecond rightFirst rightSecond : FiniteContent α}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    EvaluationEquivalent (leftFirst.append rightFirst)
      (leftSecond.append rightSecond) where
  measure_eq event := by
    rw [leftFirst.append_measure, leftSecond.append_measure,
      leftEquivalent.measure_eq event, rightEquivalent.measure_eq event]
  integral_eq value := by
    rw [leftFirst.append_integral, leftSecond.append_integral,
      leftEquivalent.integral_eq value, rightEquivalent.integral_eq value]

/-- Restriction by the same executable event preserves content
equivalence. -/
theorem restrict {α : Type} {left right : FiniteContent α}
    (equivalent : EvaluationEquivalent left right)
    (condition : α → Bool) :
    EvaluationEquivalent (left.restrict condition)
      (right.restrict condition) where
  measure_eq event := by
    rw [left.restrict_measure, right.restrict_measure,
      equivalent.measure_eq]
  integral_eq value := by
    rw [left.restrict_integral, right.restrict_integral,
      equivalent.integral_eq]

/-- Pushforward preserves content equivalence. -/
theorem map {α β : Type} {left right : FiniteContent α}
    (equivalent : EvaluationEquivalent left right) (function : α → β) :
    EvaluationEquivalent (left.map function) (right.map function) where
  measure_eq event := by
    rw [left.map_measure, right.map_measure, equivalent.measure_eq]
  integral_eq value := by
    rw [left.map_integral, right.map_integral, equivalent.integral_eq]

/-- Cartesian product preserves content equivalence in both factors. -/
theorem product {α β : Type}
    {leftFirst leftSecond : FiniteContent α}
    {rightFirst rightSecond : FiniteContent β}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    EvaluationEquivalent (leftFirst.product rightFirst)
      (leftSecond.product rightSecond) := by
  apply of_integral_eq
  intro value
  rw [leftFirst.product_integral, leftSecond.product_integral]
  calc
    leftFirst.integral (fun leftItem =>
          rightFirst.integral (fun rightItem => value (leftItem, rightItem))) =
        leftFirst.integral (fun leftItem =>
          rightSecond.integral
            (fun rightItem => value (leftItem, rightItem))) := by
      exact leftFirst.integral_congr _ _ (fun leftItem =>
        rightEquivalent.integral_eq
          (fun rightItem => value (leftItem, rightItem)))
    _ = leftSecond.integral (fun leftItem =>
          rightSecond.integral
            (fun rightItem => value (leftItem, rightItem))) :=
      leftEquivalent.integral_eq _

end EvaluationEquivalent

/-- Executably merge repeated payloads in an unnormalised content table. -/
def consolidate {α : Type} [DecidableEq α]
    (content : FiniteContent α) : FiniteContent α :=
  ⟨consolidateAtoms content.atoms⟩

theorem consolidate_noRepeatedPayloads {α : Type} [DecidableEq α]
    (content : FiniteContent α) :
    NoRepeatedPayloads content.consolidate.atoms :=
  consolidateAtoms_noRepeatedPayloads content.atoms

theorem consolidate_atoms_length_le {α : Type} [DecidableEq α]
    (content : FiniteContent α) :
    content.consolidate.atoms.length ≤ content.atoms.length :=
  consolidateAtoms_length_le content.atoms

/-- Consolidation changes table layout but no exact finite evaluation. -/
theorem consolidate_evaluationEquivalent {α : Type} [DecidableEq α]
    (content : FiniteContent α) :
    EvaluationEquivalent content.consolidate content where
  measure_eq event := eventWeight_consolidateAtoms event content.atoms
  integral_eq value :=
    expectationWeight_consolidateAtoms value content.atoms

end FiniteContent

end FiniteMeasure
