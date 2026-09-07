import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Triangles.Isosceles

/-!
# Divine Proportions, Chapter 10: right triangles

The midpoint characterization is proved after clearing the finite factor
four.  The intermediate median-quadrance identity is useful again for the
later Median quadrance theorem.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  apply eq_of_mul_eq_mul_left factorNonzero
  calc
    factor * left = left * factor := by ring1
    _ = right * factor := productsEqual
    _ = factor * right := by ring1

private theorem target_sub_midpoint_coordinate_mul_two
    (first second target : K) (twoNonzero : (2 : K) ≠ 0) :
    (target - (first + second) / 2) * 2 =
      2 * target - first - second := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (target - (first + second) * (2 : K)⁻¹) * 2 =
        2 * target - (first + second) * (2 * (2 : K)⁻¹) := by ring1
    _ = 2 * target - first - second := by rw [twoCancel]; ring1

/-- Denominator-cleared median quadrance identity. -/
theorem median_quadrance_cleared
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (midpoint first second) third * 4 =
      2 * quadrance first third + 2 * quadrance second third -
        quadrance first second := by
  rw [show (4 : K) = 2 * 2 by ring1]
  unfold quadrance midpoint
  change
    ((third.x - (first.x + second.x) / 2) ^ 2 +
        (third.y - (first.y + second.y) / 2) ^ 2) * (2 * 2) =
      2 * ((third.x - first.x) ^ 2 + (third.y - first.y) ^ 2) +
        2 * ((third.x - second.x) ^ 2 + (third.y - second.y) ^ 2) -
        ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2)
  calc
    ((third.x - (first.x + second.x) / 2) ^ 2 +
          (third.y - (first.y + second.y) / 2) ^ 2) * (2 * 2) =
      ((third.x - (first.x + second.x) / 2) * 2) ^ 2 +
        ((third.y - (first.y + second.y) / 2) * 2) ^ 2 := by ring1
    _ = (2 * third.x - first.x - second.x) ^ 2 +
        (2 * third.y - first.y - second.y) ^ 2 := by
      rw [target_sub_midpoint_coordinate_mul_two first.x second.x third.x
        twoNonzero,
        target_sub_midpoint_coordinate_mul_two first.y second.y third.y
          twoNonzero]
    _ = 2 * ((third.x - first.x) ^ 2 + (third.y - first.y) ^ 2) +
        2 * ((third.x - second.x) ^ 2 + (third.y - second.y) ^ 2) -
        ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) := by ring1

/-- Theorem 70 (Right midpoint): the midpoint of `A₁A₂` is equidistant from
`A₁` and `A₃` exactly when the vertex at `A₃` is right. -/
theorem right_midpoint [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    quadrance (midpoint first second) first =
        quadrance (midpoint first second) third ↔
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct) := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have endpointCleared :
      quadrance (midpoint first second) first * 4 =
        quadrance first second := by
    rw [midpoint_quadrance first second twoNonzero]
    exact RFAP.ExplicitField.div_mul_cancel _ fourNonzero
  have thirdCleared := median_quadrance_cleared first second third twoNonzero
  constructor
  · intro equalMidpointQuadrances
    have clearedEqual :
        quadrance first second =
          2 * quadrance first third + 2 * quadrance second third -
            quadrance first second := by
      calc
        quadrance first second =
            quadrance (midpoint first second) first * 4 :=
          endpointCleared.symm
        _ = quadrance (midpoint first second) third * 4 := by
          rw [equalMidpointQuadrances]
        _ = 2 * quadrance first third + 2 * quadrance second third -
            quadrance first second := thirdCleared
    have pythagoras :
        quadrance second third + quadrance first third =
          quadrance first second := by
      apply eq_of_mul_eq_mul_left twoNonzero
      calc
        2 * (quadrance second third + quadrance first third) =
            (2 * quadrance first third + 2 * quadrance second third -
              quadrance first second) + quadrance first second := by ring1
        _ = quadrance first second + quadrance first second := by
          rw [← clearedEqual]
        _ = 2 * quadrance first second := by ring1
    exact (pythagoras_iff_perpendicular first second third
      firstThirdDistinct secondThirdDistinct twoNonzero).1 pythagoras
  · intro perpendicular
    have pythagoras :=
      (pythagoras_iff_perpendicular first second third
        firstThirdDistinct secondThirdDistinct twoNonzero).2 perpendicular
    apply eq_of_mul_eq_mul_right fourNonzero
    calc
      quadrance (midpoint first second) first * 4 =
          quadrance first second := endpointCleared
      _ = 2 * quadrance first third + 2 * quadrance second third -
          quadrance first second := by rw [← pythagoras]; ring1
      _ = quadrance (midpoint first second) third * 4 := thirdCleared.symm

end DivineProportions
