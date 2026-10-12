module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Density.Witness
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Evaluation equivalence of finite contents

Finite contents retain their displayed atom-table layout.  Observational
equivalence records equality of every executable event measure and every
rational integral without quotienting those tables.  Consolidation and the
basic finite-content operations respect this relation.
-/

namespace Purelib.Measure

namespace Content

open Purelib.Data.Rat in
/-- Require the two original contents to agree on every Boolean event and rational observable integral.

The relation keeps both finite occurrence lists intact. It compares their event measurements and integral readbacks
without identifying or replacing their stored representations. -/
structure EvaluationEquivalent {α : Type}
    (left right : Content α) : Prop where
  /-- Every Boolean event has the same measurement in the two original contents. -/ measure_eq : ∀ event : α → Bool,
    left.measure event = right.measure event
  /-- Every rational observable has the same integral in the two original contents. -/ integral_eq : ∀ value : α →
    Fraction.Rational,
    left.integral value = right.integral value

namespace EvaluationEquivalent

open Purelib.Data.Rat in
/-- Equality of all rational integrals gives evaluation equivalence of the same retained contents. -/
theorem of_integral_eq {α : Type} {left right : Content α}
    (integralEqual : ∀ value : α → Fraction.Rational,
      left.integral value = right.integral value) :
    EvaluationEquivalent left right where
  measure_eq event := by
    rw [← left.integral_indicator event, ← right.integral_indicator event]
    exact integralEqual _
  integral_eq := integralEqual

/-- Every retained content is evaluation equivalent to itself. -/
theorem refl {α : Type} (content : Content α) :
    EvaluationEquivalent content content where
  measure_eq _ := rfl
  integral_eq _ := rfl

/-- Reverse evaluation equivalence of the two retained contents. -/
theorem symm {α : Type} {left right : Content α}
    (equivalent : EvaluationEquivalent left right) :
    EvaluationEquivalent right left where
  measure_eq event := (equivalent.measure_eq event).symm
  integral_eq value := (equivalent.integral_eq value).symm

/-- Compose evaluation equivalence through the same retained middle content. -/
theorem trans {α : Type} {first second third : Content α}
    (firstSecond : EvaluationEquivalent first second)
    (secondThird : EvaluationEquivalent second third) :
    EvaluationEquivalent first third where
  measure_eq event :=
    (firstSecond.measure_eq event).trans (secondThird.measure_eq event)
  integral_eq value :=
    (firstSecond.integral_eq value).trans (secondThird.integral_eq value)

/-- Appending pairwise evaluation-equivalent contents preserves evaluation equivalence. -/
theorem append {α : Type}
    {leftFirst leftSecond rightFirst rightSecond : Content α}
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

/-- Restricting evaluation-equivalent contents by the same Boolean condition preserves evaluation equivalence. -/
theorem restrict {α : Type} {left right : Content α}
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

/-- Mapping evaluation-equivalent contents by the same payload function preserves evaluation equivalence. -/
theorem map {α β : Type} {left right : Content α}
    (equivalent : EvaluationEquivalent left right) (function : α → β) :
    EvaluationEquivalent (left.map function) (right.map function) where
  measure_eq event := by
    rw [left.map_measure, right.map_measure, equivalent.measure_eq]
  integral_eq value := by
    rw [left.map_integral, right.map_integral, equivalent.integral_eq]

/-- Taking products of two evaluation-equivalent pairs preserves evaluation equivalence. -/
theorem product {α β : Type}
    {leftFirst leftSecond : Content α}
    {rightFirst rightSecond : Content β}
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

/-- Consolidate equal payload weights in the exact retained content occurrence list. -/
def consolidate {α : Type} [DecidableEq α]
    (content : Content α) : Content α :=
  ⟨consolidateAtoms content.atoms⟩

/-- The consolidated content has no repeated payloads. -/
theorem consolidate_noRepeatedPayloads {α : Type} [DecidableEq α]
    (content : Content α) :
    NoRepeatedPayloads content.consolidate.atoms :=
  consolidateAtoms_noRepeatedPayloads content.atoms

/-- The consolidated content has at most the original occurrence count. -/
theorem consolidate_atoms_length_le {α : Type} [DecidableEq α]
    (content : Content α) :
    content.consolidate.atoms.length ≤ content.atoms.length :=
  consolidateAtoms_length_le content.atoms

/-- The exact consolidated content agrees with the original on every event and rational integral. -/
theorem consolidate_evaluationEquivalent {α : Type} [DecidableEq α]
    (content : Content α) :
    EvaluationEquivalent content.consolidate content where
  measure_eq event := eventWeight_consolidateAtoms event content.atoms
  integral_eq value :=
    expectationWeight_consolidateAtoms value content.atoms

end Content

end Purelib.Measure
