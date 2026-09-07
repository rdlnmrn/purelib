import DivineProportions.Trigonometry.Quadrea
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Exercise 5.13

The source's maximum claim is stated without a supremum or completed real
object.  For every requested third quadrance, quadrea is bounded above by
`4 Q₁ Q₂`; equality holds exactly at the Pythagorean value.  The geometric
form then identifies equality with perpendicularity at the third vertex.
-/

namespace DivineProportions

namespace ExerciseFiveThirteen

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The finite scalar content of Exercise 5.13: with `q₁` and `q₂` fixed,
every requested `q₃` gives quadrea at most `4q₁q₂`, and equality holds
exactly when `q₁+q₂=q₃`. -/
theorem exercise_5_13_scalar (q₁ q₂ q₃ : Rational) :
    archimedesFunction q₁ q₂ q₃ ≤ 4 * q₁ * q₂ ∧
      (archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ ↔
        q₁ + q₂ = q₃) := by
  have upperBound : archimedesFunction q₁ q₂ q₃ ≤ 4 * q₁ * q₂ := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (q₁ + q₂ - q₃) ^ 2 :=
        RFAP.ConstructiveFraction.sq_nonneg_direct _
      _ = 4 * q₁ * q₂ - archimedesFunction q₁ q₂ q₃ := by
        unfold archimedesFunction
        ring1
  refine ⟨upperBound, ?_⟩
  constructor
  · intro maximal
    have squareZero : (q₁ + q₂ - q₃) ^ 2 = 0 := by
      calc
        (q₁ + q₂ - q₃) ^ 2 =
            4 * q₁ * q₂ - archimedesFunction q₁ q₂ q₃ := by
              unfold archimedesFunction
              ring1
        _ = 0 := by rw [maximal]; ring1
    have differenceZero :=
      (RFAP.ConstructiveFraction.sq_eq_zero_direct
        (q₁ + q₂ - q₃)).1 squareZero
    exact sub_eq_zero.mp differenceZero
  · intro pythagoras
    unfold archimedesFunction
    rw [← pythagoras]
    ring1

private theorem rational_two_nonzero : (2 : Rational) ≠ 0 := by decide

/-- Exercise 5.13 in its geometric form.  The pointwise upper bound is the
constructive meaning of “maximum possible”, and its equality case is exactly
a right vertex at `third`. -/
theorem exercise_5_13
    (first second third : Point Rational)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third) :
    quadrea first second third ≤
        4 * quadrance second third * quadrance first third ∧
      (quadrea first second third =
          4 * quadrance second third * quadrance first third ↔
        (lineThrough first third firstThirdDistinct).Perpendicular
          (lineThrough second third secondThirdDistinct)) := by
  have scalarResult := exercise_5_13_scalar
    (quadrance second third)
    (quadrance first third)
    (quadrance first second)
  constructor
  · exact scalarResult.1
  · change
      archimedesFunction
          (quadrance second third)
          (quadrance first third)
          (quadrance first second) =
          4 * quadrance second third * quadrance first third ↔ _
    rw [scalarResult.2]
    exact pythagoras_iff_perpendicular first second third
      firstThirdDistinct secondThirdDistinct rational_two_nonzero

end ExerciseFiveThirteen

end DivineProportions
