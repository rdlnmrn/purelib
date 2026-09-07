import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.MaximalCoupling
import FiniteMeasure.ProductTotalVariation

/-!
# Products of finite couplings

Two displayed law couplings can be sampled independently and their
coordinates regrouped.  Under equality, the product mismatches exactly when
at least one component mismatches, giving the rational formula
`1 - (1 - d₁) * (1 - d₂)`.  Product maximal couplings therefore sharpen the
additive total-variation tensorization bound.
-/

namespace FiniteMeasure

namespace Distribution

/-- Independent pushforwards commute with a displayed finite product up to
exact evaluation equivalence. -/
theorem productMap_evaluationEquivalent {α β γ δ : Type}
    (left : Distribution α) (right : Distribution β)
    (leftMap : α → γ) (rightMap : β → δ) :
    EvaluationEquivalent
      ((left.product right).map fun pair =>
        (leftMap pair.1, rightMap pair.2))
      ((left.map leftMap).product (right.map rightMap)) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [(left.product right).map_expectation,
    left.product_expectation_iterated,
    (left.map leftMap).product_expectation_iterated,
    left.map_expectation]
  exact left.expectation_congr _ _ (fun leftItem => by
    rw [right.map_expectation])

end Distribution

namespace LawCoupling

/-- Independent product of two named-law couplings. -/
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

/-- Exact mismatch formula for the independent product of two couplings under
componentwise equality. -/
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
      by_cases firstEqual : pair.1.1 = pair.1.2
      · by_cases secondEqual : pair.2.1 = pair.2.2
        · simp [Coupling.mismatchEvent, equalityRelation, regroup, bothMatch,
            firstMatch, secondMatch, complementEvent, firstEqual, secondEqual]
        · simp [Coupling.mismatchEvent, equalityRelation, regroup, bothMatch,
            firstMatch, secondMatch, complementEvent, firstEqual, secondEqual]
      · simp [Coupling.mismatchEvent, equalityRelation, regroup, bothMatch,
          firstMatch, secondMatch, complementEvent, firstEqual])
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

/-- Sharp finite product tensorization obtained from independent maximal
couplings. -/
theorem totalVariationDistance_product_le_one_sub_mul
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (leftFirst rightFirst : Distribution α)
    (leftSecond rightSecond : Distribution β) :
    (leftFirst.product leftSecond).totalVariationDistance
        (rightFirst.product rightSecond) ≤
      1 - (1 - leftFirst.totalVariationDistance rightFirst) *
        (1 - leftSecond.totalVariationDistance rightSecond) := by
  let first := leftFirst.maximalLawCoupling rightFirst
  let second := leftSecond.maximalLawCoupling rightSecond
  have coupled := (first.product second)
    |>.totalVariationDistance_le_mismatchProbability
  rw [first.product_mismatchProbability_eq second,
    leftFirst.maximalLawCoupling_mismatchProbability rightFirst,
    leftSecond.maximalLawCoupling_mismatchProbability rightSecond] at coupled
  exact coupled

/-- Sharp finite IID amplification bound from repeated independent maximal
couplings. -/
theorem iidSamples_totalVariationDistance_le_one_sub_pow
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ∀ count : Nat,
      (left.iidSamples count).totalVariationDistance
          (right.iidSamples count) ≤
        1 - (1 - left.totalVariationDistance right) ^ count
  | 0 => by
      have zero : (left.iidSamples 0).totalVariationDistance
          (right.iidSamples 0) = 0 := by
        apply (left.iidSamples 0)
          |>.totalVariationDistance_eq_zero_iff_evaluationEquivalent
            (right.iidSamples 0) |>.2
        rw [left.iidSamples_zero, right.iidSamples_zero]
        exact EvaluationEquivalent.refl (Distribution.pure [])
      rw [zero, pow_zero]
      change (0 : Coordinate) ≤ 0
      exact le_rfl
  | count + 1 => by
      rw [left.iidSamples_succ, right.iidSamples_succ]
      let distance := left.totalVariationDistance right
      let tailDistance := (left.iidSamples count).totalVariationDistance
        (right.iidSamples count)
      let tailBound : Coordinate := 1 - (1 - distance) ^ count
      have distanceAtMostOne : distance ≤ 1 :=
        left.totalVariationDistance_le_one right
      have complementNonnegative : 0 ≤ 1 - distance :=
        RFAP.ConstructiveFraction.sub_nonneg_direct distanceAtMostOne
      have tailLe : tailDistance ≤ tailBound := by
        exact iidSamples_totalVariationDistance_le_one_sub_pow
          left right count
      have complementOrder : 1 - tailBound ≤ 1 - tailDistance := by
        exact RFAP.ConstructiveFraction.sub_le_sub_left_direct tailLe 1
      have productOrder :
          (1 - distance) * (1 - tailBound) ≤
            (1 - distance) * (1 - tailDistance) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          complementOrder complementNonnegative
      calc
        ((left.product (left.iidSamples count)).map fun pair =>
              pair.1 :: pair.2).totalVariationDistance
            ((right.product (right.iidSamples count)).map fun pair =>
              pair.1 :: pair.2) ≤
          (left.product (left.iidSamples count)).totalVariationDistance
            (right.product (right.iidSamples count)) :=
          (left.product (left.iidSamples count)).totalVariationDistance_map_le
            (right.product (right.iidSamples count))
            (fun pair => pair.1 :: pair.2)
        _ ≤ 1 - (1 - distance) * (1 - tailDistance) := by
          exact left.totalVariationDistance_product_le_one_sub_mul right
            (left.iidSamples count) (right.iidSamples count)
        _ ≤ 1 - (1 - distance) * (1 - tailBound) :=
          RFAP.ConstructiveFraction.sub_le_sub_left_direct productOrder 1
        _ = 1 - (1 - left.totalVariationDistance right) ^ (count + 1) := by
          dsimp only [distance, tailBound]
          rw [pow_succ]
          ring1

end Distribution

end FiniteMeasure
