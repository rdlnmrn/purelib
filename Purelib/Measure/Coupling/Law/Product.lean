module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring

import Purelib.Data.Bool.Relation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Coupling.Basic
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Equivalence
public import Purelib.Measure.Distribution.Product.Equivalence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Products of finite couplings

Two displayed law couplings can be sampled independently and their
coordinates regrouped.  Under equality, the product mismatches exactly when
at least one component mismatches, giving the rational formula
`1 - (1 - d₁) * (1 - d₂)`.  Product maximal couplings therefore sharpen the
additive total-variation tensorization bound.
-/

namespace Purelib.Measure

namespace Distribution
end Distribution

namespace LawCoupling

/-- Combine two retained law couplings by taking their exact joint product and regrouping its coordinates.

The original marginal evaluation certificates establish the specified product laws while preserving both input couplings
and their exact joint occurrences. -/
def product {α β γ δ : Type}
    {leftFirst : Distribution α} {rightFirst : Distribution β}
    {leftSecond : Distribution γ} {rightSecond : Distribution δ}
    (first : LawCoupling leftFirst rightFirst)
    (second : LawCoupling leftSecond rightSecond) :
    LawCoupling (leftFirst.product leftSecond)
      (rightFirst.product rightSecond) := by
  let regroup : (α × β) × (γ × δ) → (α × γ) × (β × δ) :=
    fun pair => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))
  let joint := (first.coupling.joint.product second.coupling.joint).map regroup
  let coupling : Coupling (α × γ) (β × δ) := ⟨joint⟩
  have leftLayout : Distribution.EvaluationEquivalent
      coupling.leftMarginal
      (first.coupling.leftMarginal.product
        second.coupling.leftMarginal) := by
    have composed :=
      (first.coupling.joint.product second.coupling.joint)
        |>.map_map_evaluationEquivalent regroup (fun pair => pair.1)
    have separated :=
      first.coupling.joint.productMap_evaluationEquivalent
        second.coupling.joint (fun pair => pair.1) (fun pair => pair.1)
    exact composed.trans separated
  have rightLayout : Distribution.EvaluationEquivalent
      coupling.rightMarginal
      (first.coupling.rightMarginal.product
        second.coupling.rightMarginal) := by
    have composed :=
      (first.coupling.joint.product second.coupling.joint)
        |>.map_map_evaluationEquivalent regroup (fun pair => pair.2)
    have separated :=
      first.coupling.joint.productMap_evaluationEquivalent
        second.coupling.joint (fun pair => pair.2) (fun pair => pair.2)
    exact composed.trans separated
  exact
    { coupling := coupling
      leftEquivalent := leftLayout.trans
        (first.leftEquivalent.product second.leftEquivalent)
      rightEquivalent := rightLayout.trans
        (first.rightEquivalent.product second.rightEquivalent) }

/-- The product coupling's equality mismatch is one minus the product of the two original equality-match probabilities.
-/
theorem product_mismatchProbability_eq {α β : Type}
    [DecidableEq α] [DecidableEq β]
    {leftFirst rightFirst : Distribution α}
    {leftSecond rightSecond : Distribution β}
    (first : LawCoupling leftFirst rightFirst)
    (second : LawCoupling leftSecond rightSecond) :
    (first.product second).mismatchProbability equalityRelation =
      1 - (1 - first.mismatchProbability equalityRelation) *
        (1 - second.mismatchProbability equalityRelation) := by
  let firstMatch : α × α → Bool := fun pair =>
    equalityRelation pair.1 pair.2
  let secondMatch : β × β → Bool := fun pair =>
    equalityRelation pair.1 pair.2
  let bothMatch : (α × α) × (β × β) → Bool := fun pair =>
    firstMatch pair.1 && secondMatch pair.2
  let regroup : (α × α) × (β × β) → (α × β) × (α × β) :=
    fun pair => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))
  let raw := first.coupling.joint.product second.coupling.joint
  have mismatchSame : raw.probability (fun pair =>
      Coupling.mismatchEvent equalityRelation (regroup pair)) =
      raw.probability (complementEvent bothMatch) :=
    raw.probability_congr _ _ (fun pair => by
      change (!equalityRelation (pair.1.1, pair.2.1) (pair.1.2, pair.2.2)) =
        !(equalityRelation pair.1.1 pair.1.2 && equalityRelation pair.2.1 pair.2.2)
      rewrite [equalityRelation]
      change (!decide ((pair.1.1, pair.2.1) = (pair.1.2, pair.2.2))) =
        !(decide (pair.1.1 = pair.1.2) && decide (pair.2.1 = pair.2.2))
      by_cases firstEqual : pair.1.1 = pair.1.2
      · by_cases secondEqual : pair.2.1 = pair.2.2
        · have paired := congrArg₂ Prod.mk firstEqual secondEqual
          rw [decide_eq_true paired, decide_eq_true firstEqual, decide_eq_true secondEqual]
          rfl
        · have unpaired : (pair.1.1, pair.2.1) ≠ (pair.1.2, pair.2.2) :=
            fun equal => secondEqual (congrArg Prod.snd equal)
          rw [decide_eq_false unpaired, decide_eq_true firstEqual, decide_eq_false secondEqual]
          rfl
      · have unpaired : (pair.1.1, pair.2.1) ≠ (pair.1.2, pair.2.2) :=
          fun equal => firstEqual (congrArg Prod.fst equal)
        rw [decide_eq_false unpaired, decide_eq_false firstEqual]
        rfl)
  have firstSplit := first.coupling.joint.probability_add_complement firstMatch
  have secondSplit :=
    second.coupling.joint.probability_add_complement secondMatch
  have rawSplit := raw.probability_add_complement bothMatch
  have matchProduct : raw.probability bothMatch =
      first.coupling.joint.probability firstMatch *
        second.coupling.joint.probability secondMatch := by
    exact first.coupling.joint.product_probability_rectangle
      second.coupling.joint firstMatch secondMatch
  have firstMismatch : first.mismatchProbability equalityRelation =
      first.coupling.joint.probability (complementEvent firstMatch) := rfl
  have secondMismatch : second.mismatchProbability equalityRelation =
      second.coupling.joint.probability (complementEvent secondMatch) := rfl
  rw [firstMismatch, secondMismatch]
  unfold product mismatchProbability Coupling.mismatchProbability
  change ((raw.map regroup).probability
      (Coupling.mismatchEvent equalityRelation)) = _
  rw [raw.map_probability, mismatchSame]
  have firstMatchEq : first.coupling.joint.probability firstMatch =
      1 - first.coupling.joint.probability (complementEvent firstMatch) := by
    rw [← firstSplit]
    ring1
  have secondMatchEq : second.coupling.joint.probability secondMatch =
      1 - second.coupling.joint.probability (complementEvent secondMatch) := by
    rw [← secondSplit]
    ring1
  calc
    raw.probability (complementEvent bothMatch) =
        1 - raw.probability bothMatch := by
      rw [← rawSplit]
      ring1
    _ = 1 - first.coupling.joint.probability firstMatch *
        second.coupling.joint.probability secondMatch := by
      rw [matchProduct]
    _ = 1 -
        (1 - first.coupling.joint.probability (complementEvent firstMatch)) *
          (1 - second.coupling.joint.probability
            (complementEvent secondMatch)) := by
      rw [firstMatchEq, secondMatchEq]

end LawCoupling

namespace Distribution
end Distribution

end Purelib.Measure

end
