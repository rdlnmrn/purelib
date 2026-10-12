module
public import Purelib.Algebra.Proportion.Three.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib.Algebra.Proportion.Three.Basic (ThreeProportion)

/-! Independent cross-product conditions on three-proportions over a nontrivial commutative ring. -/

@[expose] public section

namespace Purelib.Algebra

variable {K : Type*}

section ThreeProportionExamples

variable [CommRing K] [Nontrivial K]

/-- Each cross-product condition on three-proportions is independent of the other two.

Three explicit pairs over a nontrivial commutative ring each satisfy two conditions and fail the third. -/
theorem Proportion.Three.Independence.exercise_2_4 :
    let leftFirst : ThreeProportion K :=
      ⟨1, 0, 0, Or.inl one_ne_zero⟩
    let rightFirst : ThreeProportion K :=
      ⟨1, 1, 0, Or.inl one_ne_zero⟩
    let leftSecond : ThreeProportion K :=
      ⟨0, 1, 0, Or.inr (Or.inl one_ne_zero)⟩
    let rightSecond : ThreeProportion K :=
      ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero)⟩
    let rightThird : ThreeProportion K :=
      ⟨1, 0, 1, Or.inl one_ne_zero⟩
    (¬ ThreeProportion.FirstCondition
        leftFirst rightFirst ∧
      ThreeProportion.SecondCondition
        leftFirst rightFirst ∧
      ThreeProportion.ThirdCondition
        leftFirst rightFirst) ∧
    (ThreeProportion.FirstCondition
        leftSecond rightSecond ∧
      ¬ ThreeProportion.SecondCondition
        leftSecond rightSecond ∧
      ThreeProportion.ThirdCondition
        leftSecond rightSecond) ∧
    (ThreeProportion.FirstCondition
        leftFirst rightThird ∧
      ThreeProportion.SecondCondition
        leftFirst rightThird ∧
      ¬ ThreeProportion.ThirdCondition
        leftFirst rightThird) := by
  unfold ThreeProportion.FirstCondition ThreeProportion.SecondCondition
    ThreeProportion.ThirdCondition
  constructor
  · exact ⟨by
      intro condition
      exact one_ne_zero ((one_mul (1 : K)).symm.trans
        (condition.trans (mul_zero (1 : K)))), by ring1, by ring1⟩
  constructor
  · exact ⟨by ring1, by
      intro condition
      exact one_ne_zero ((one_mul (1 : K)).symm.trans
        (condition.trans (mul_zero (1 : K)))), by ring1⟩
  · exact ⟨by ring1, by ring1,
      by
        intro condition
        exact one_ne_zero ((one_mul (1 : K)).symm.trans
          (condition.symm.trans (zero_mul (1 : K))))⟩

end ThreeProportionExamples

end Purelib.Algebra

end
