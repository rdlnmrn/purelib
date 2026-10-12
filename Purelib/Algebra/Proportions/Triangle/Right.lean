module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry.Spread.Triple

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

namespace Purelib.Algebra.Proportions.Triangle.Right

variable {K : Type*} [ExplicitField K]

/-- A right spread triple and a cleared triangle ratio give a linear spread identity.

The two non-right spreads sum to one, so no denominator cancellation is needed. -/
theorem exercise_11_1_cleared [DecidableEq K]
    (r₁ r₂ s₁ s₂ R₁ R₂ : K)
    (rightTriangle : TripleSpread.SpreadTriple s₁ s₂ 1)
    (triangleProportion :
      r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂) :
    s₁ * (r₁ * R₂ + r₂ * R₁) = r₁ * R₂ := by
  have spreadSum : s₁ + s₂ = 1 :=
    (Triple.spreadTriple_one_iff s₁ s₂).1 rightTriangle
  calc
    s₁ * (r₁ * R₂ + r₂ * R₁) =
        s₁ * (r₁ * R₂) + (s₁ * R₁) * r₂ := by ring1
    _ = s₁ * (r₁ * R₂) + r₁ * (s₂ * R₂) := by
      rw [triangleProportion]
    _ = (s₁ + s₂) * (r₁ * R₂) := by ring1
    _ = r₁ * R₂ := by rw [spreadSum, one_mul]

open Purelib in
/-- Express one spread of a right triangle as a reciprocal ratio.

The retained triangle proportion and nonzero product of the specified ratio and quadrance justify the displayed
divisions. -/
theorem exercise_11_1 [DecidableEq K]
    (r₁ r₂ s₁ s₂ R₁ R₂ : K)
    (r₁Nonzero : r₁ ≠ 0) (R₂Nonzero : R₂ ≠ 0)
    (rightTriangle : TripleSpread.SpreadTriple s₁ s₂ 1)
    (triangleProportion :
      r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂) :
    s₁ = (1 + (r₂ * R₁) / (r₁ * R₂))⁻¹ := by
  let denominator := r₁ * R₂
  let expression := 1 + (r₂ * R₁) / denominator
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero r₁Nonzero R₂Nonzero
  have cleared := exercise_11_1_cleared r₁ r₂ s₁ s₂ R₁ R₂
    rightTriangle triangleProportion
  have expressionProduct : s₁ * expression = 1 := by
    apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      (s₁ * expression) * denominator =
          s₁ * (denominator + ((r₂ * R₁) / denominator) *
            denominator) := by
        unfold expression
        ring1
      _ = s₁ * (denominator + r₂ * R₁) := by
        rw [ExplicitField.div_mul_cancel _ denominatorNonzero]
      _ = denominator := by
        simpa only [denominator] using cleared
      _ = 1 * denominator := by ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply denominatorNonzero
    calc
      denominator = denominator * 1 := by rw [mul_one]
      _ = denominator * 0 := by rw [oneZero]
      _ = 0 := by rw [mul_zero]
  have expressionNonzero : expression ≠ 0 := by
    intro expressionZero
    apply oneNonzero
    calc
      1 = s₁ * expression := expressionProduct.symm
      _ = 0 := by rw [expressionZero, mul_zero]
  apply ExplicitField.eq_of_mul_eq_mul_right expressionNonzero
  calc
    s₁ * expression = 1 := expressionProduct
    _ = expression⁻¹ * expression := by
      rw [show expression⁻¹ * expression = expression * expression⁻¹ by
        ring1, ExplicitField.mul_inv_cancel expression
          expressionNonzero]
end Purelib.Algebra.Proportions.Triangle.Right

end
