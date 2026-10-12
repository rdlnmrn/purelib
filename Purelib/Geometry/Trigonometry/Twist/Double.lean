module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.Ratio
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: isosceles triangles

The scalar forms isolate the finite cancellations used by the geometric
statements.  They apply uniformly to ratios obtained from rational triangles
or from triangles over explicit finite fields.
-/

namespace Purelib.Geometry.Trigonometry.Twist.Double

variable {K : Type*} [ExplicitField K]

/-- Exercise 10.1. The first premise is the complemented Equal-spreads formula, while the last two premises are the
spread/cross definitions of the two twists. Nonzero crosses are precisely the finite denominators required for those
twists to be defined. -/
theorem exercise_10_1
    (c c₃ t t₃ : K) (cNonzero : c ≠ 0) (c₃Nonzero : c₃ ≠ 0)
    (thirdCross : c₃ = 1 - 4 * (1 - c) * c)
    (twistValue : t = (1 - c) / c)
    (thirdTwistValue : t₃ = (1 - c₃) / c₃) :
    c₃ = (2 * c - 1) ^ 2 ∧
      t₃ = 4 * t / (1 - t) ^ 2 := by
  have thirdCrossFormula : c₃ = (2 * c - 1) ^ 2 := by
    rw [thirdCross]
    ring1
  have inverseCancel : c * c⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel c cNonzero
  have oneMinusTwist : 1 - t = (2 * c - 1) * c⁻¹ := by
    rw [twistValue]
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      1 - (1 - c) * c⁻¹ =
          (2 * c - 1) * c⁻¹ + (1 - c * c⁻¹) := by ring1
      _ = (2 * c - 1) * c⁻¹ := by rw [inverseCancel]; ring1
  have crossFactorNonzero : 2 * c - 1 ≠ 0 := by
    intro factorZero
    apply c₃Nonzero
    rw [thirdCrossFormula, factorZero]
    ring1
  have oneMinusTwistNonzero : 1 - t ≠ 0 := by
    rw [oneMinusTwist]
    exact ExplicitField.mul_ne_zero crossFactorNonzero
      (ExplicitField.inv_ne_zero cNonzero)
  have oneMinusTwistSquareNonzero : (1 - t) ^ 2 ≠ 0 := by
    simpa [pow_two] using ExplicitField.mul_ne_zero
      oneMinusTwistNonzero oneMinusTwistNonzero
  have oneMinusThirdCross : 1 - c₃ = 4 * c * (1 - c) := by
    rw [thirdCrossFormula]
    ring1
  constructor
  · exact thirdCrossFormula
  · rw [thirdTwistValue]
    apply Ratio.ratio_eq_of_cross_product c₃Nonzero
      oneMinusTwistSquareNonzero
    rw [oneMinusThirdCross, oneMinusTwist, twistValue,
      thirdCrossFormula]
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      4 * c * (1 - c) * (((2 * c - 1) * c⁻¹) ^ 2) =
          4 * (1 - c) * (2 * c - 1) ^ 2 *
            (c * c⁻¹) * c⁻¹ := by ring1
      _ = 4 * ((1 - c) * c⁻¹) * (2 * c - 1) ^ 2 := by
        rw [inverseCancel]
        ring1
end Purelib.Geometry.Trigonometry.Twist.Double

end
