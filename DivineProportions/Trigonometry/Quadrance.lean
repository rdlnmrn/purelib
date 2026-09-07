import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Plane.Affine
import DivineProportions.Algebra.FieldFive

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The quadrance between two Cartesian points. -/
def quadrance (first second : Point K) : K :=
  (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2

theorem quadrance_symm (first second : Point K) :
    quadrance first second = quadrance second first := by
  unfold quadrance
  ring1

theorem quadrance_self (point : Point K) : quadrance point point = 0 := by
  unfold quadrance
  ring1

private theorem eq_zero_of_mul_eq_zero_left [DecidableEq K]
    {left right : K} (leftNonzero : left ≠ 0) (productZero : left * right = 0) :
    right = 0 := by
  by_cases rightZero : right = 0
  · exact rightZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftNonzero rightZero) productZero)

private theorem eq_zero_of_mul_eq_zero_right [DecidableEq K]
    {left right : K} (rightNonzero : right ≠ 0) (productZero : left * right = 0) :
    left = 0 := by
  by_cases leftZero : left = 0
  · exact leftZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftZero rightNonzero) productZero)

/-- Theorem 19 (Null line): the line through two distinct points is null
exactly when their quadrance is zero. -/
theorem null_line_iff_quadrance_zero [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).IsNull ↔ quadrance first second = 0 := by
  unfold Line.IsNull lineThrough quadrance
  constructor <;> intro equality
  · calc
      (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
          (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 := by ring1
      _ = 0 := equality
  · calc
      (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 =
          (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by ring1
      _ = 0 := equality

/-- Example 5.1 in a finite field: `[0,0]` and `[1,2]` are distinct in `F₅`
but have zero quadrance because `2² = -1`. -/
theorem example_5_1_fieldFive :
    quadrance
      (⟨0, 0⟩ : Point FieldFive.Element)
      (⟨1, 2⟩ : Point FieldFive.Element) = 0 := by
  decide

theorem example_5_1_fieldFive_distinct :
    (⟨0, 0⟩ : Point FieldFive.Element) ≠ ⟨1, 2⟩ := by
  decide

private theorem left_sub_midpoint_coordinate (left right : K)
    (twoNonzero : (2 : K) ≠ 0) :
    left - (left + right) / 2 = (left - right) / 2 := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    left - (left + right) * (2 : K)⁻¹ =
        (left - right) * (2 : K)⁻¹ +
          left * (1 - 2 * (2 : K)⁻¹) := by ring1
    _ = (left - right) * (2 : K)⁻¹ := by rw [twoInverse]; ring1

private theorem right_sub_midpoint_coordinate (left right : K)
    (twoNonzero : (2 : K) ≠ 0) :
    right - (left + right) / 2 = (right - left) / 2 := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    right - (left + right) * (2 : K)⁻¹ =
        (right - left) * (2 : K)⁻¹ +
          right * (1 - 2 * (2 : K)⁻¹) := by ring1
    _ = (right - left) * (2 : K)⁻¹ := by rw [twoInverse]; ring1

/-- The displayed midpoint lies on its side line. -/
theorem midpoint_on_line [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (lineThrough first second distinct).Contains (midpoint first second) := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold Line.Contains lineThrough midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (first.y - second.y) * ((first.x + second.x) * (2 : K)⁻¹) +
        (second.x - first.x) * ((first.y + second.y) * (2 : K)⁻¹) +
        (first.x * second.y - second.x * first.y) =
      (1 - 2 * (2 : K)⁻¹) *
        (first.x * second.y - second.x * first.y) := by ring1
    _ = 0 := by rw [twoInverse]; ring1

/-- The displayed midpoint has equal quadrance to the two endpoints. -/
theorem midpoint_equal_quadrance
    (first second : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (midpoint first second) first =
      quadrance (midpoint first second) second := by
  unfold quadrance
  change
    (first.x - (first.x + second.x) / 2) ^ 2 +
        (first.y - (first.y + second.y) / 2) ^ 2 =
      (second.x - (first.x + second.x) / 2) ^ 2 +
        (second.y - (first.y + second.y) / 2) ^ 2
  rw [left_sub_midpoint_coordinate first.x second.x twoNonzero,
    left_sub_midpoint_coordinate first.y second.y twoNonzero,
    right_sub_midpoint_coordinate first.x second.x twoNonzero,
    right_sub_midpoint_coordinate first.y second.y twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- The midpoint-to-endpoint quadrance is one quarter of the side quadrance.
Only characteristic two is excluded. -/
theorem midpoint_quadrance [DecidableEq K]
    (first second : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (midpoint first second) first = quadrance first second / 4 := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have scaled : quadrance (midpoint first second) first * (4 : K) =
      quadrance first second := by
    unfold quadrance
    change
      ((first.x - (first.x + second.x) / 2) ^ 2 +
        (first.y - (first.y + second.y) / 2) ^ 2) * 4 =
        (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2
    rw [left_sub_midpoint_coordinate first.x second.x twoNonzero,
      left_sub_midpoint_coordinate first.y second.y twoNonzero]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [fourAsProduct]
    calc
      (((first.x - second.x) * (2 : K)⁻¹) ^ 2 +
          ((first.y - second.y) * (2 : K)⁻¹) ^ 2) * (2 * 2) =
        ((first.x - second.x) ^ 2 + (first.y - second.y) ^ 2) *
          (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
        rw [twoInverse]
        ring1
  calc
    quadrance (midpoint first second) first =
        quadrance (midpoint first second) first * 4 * (4 : K)⁻¹ := by
      rw [mul_assoc, RFAP.ExplicitField.mul_inv_cancel 4 fourNonzero, mul_one]
    _ = quadrance first second * (4 : K)⁻¹ := by rw [scaled]
    _ = quadrance first second / 4 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]

/-- The uniqueness clause of Theorem 20: on a non-null side, the midpoint is
the only point of the line equidistant from the endpoints. -/
theorem midpoint_unique_of_equal_quadrance [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull : ¬ (lineThrough first second distinct).IsNull)
    (onLine : (lineThrough first second distinct).Contains point)
    (equalQuadrances : quadrance point first = quadrance point second) :
    point = midpoint first second := by
  have sideQuadranceNonzero : quadrance first second ≠ 0 := by
    intro sideQuadranceZero
    exact sideNonNull
      ((null_line_iff_quadrance_zero first second distinct).2 sideQuadranceZero)
  rcases affineWeights_exist first second point distinct onLine with
    ⟨leftWeight, rightWeight, weights, combination⟩
  have leftFormula : leftWeight = 1 - rightWeight := by
    calc
      leftWeight = (leftWeight + rightWeight) - rightWeight := by ring1
      _ = 1 - rightWeight := by rw [weights]
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  have fromFirst : quadrance point first =
      rightWeight ^ 2 * quadrance first second := by
    rw [← combination]
    rw [leftFormula]
    unfold quadrance affineCombination
    ring1
  have fromSecond : quadrance point second =
      leftWeight ^ 2 * quadrance first second := by
    rw [← combination]
    rw [rightFormula]
    unfold quadrance affineCombination
    ring1
  have differenceTimesSide :
      (rightWeight ^ 2 - leftWeight ^ 2) * quadrance first second = 0 := by
    calc
      (rightWeight ^ 2 - leftWeight ^ 2) * quadrance first second =
          rightWeight ^ 2 * quadrance first second -
            leftWeight ^ 2 * quadrance first second := by ring1
      _ = quadrance point first - quadrance point second := by
        rw [fromFirst, fromSecond]
      _ = 0 := by rw [equalQuadrances]; ring1
  have squareDifferenceZero : rightWeight ^ 2 - leftWeight ^ 2 = 0 :=
    eq_zero_of_mul_eq_zero_right sideQuadranceNonzero differenceTimesSide
  have weightsReversed : rightWeight + leftWeight = 1 := by
    calc
      rightWeight + leftWeight = leftWeight + rightWeight := by ring1
      _ = 1 := weights
  have weightDifferenceZero : rightWeight - leftWeight = 0 := by
    have productZero :
        (rightWeight - leftWeight) * (rightWeight + leftWeight) = 0 := by
      calc
        (rightWeight - leftWeight) * (rightWeight + leftWeight) =
            rightWeight ^ 2 - leftWeight ^ 2 := by ring1
        _ = 0 := squareDifferenceZero
    rw [weightsReversed, mul_one] at productZero
    exact productZero
  have weightsEqual : rightWeight = leftWeight := by
    calc
      rightWeight = (rightWeight - leftWeight) + leftWeight := by ring1
      _ = leftWeight := by rw [weightDifferenceZero]; ring1
  have twiceLeft : (2 : K) * leftWeight = 1 := by
    calc
      (2 : K) * leftWeight = leftWeight + rightWeight := by
        rw [weightsEqual]
        ring1
      _ = 1 := weights
  have leftTimesTwo : leftWeight * (2 : K) = 1 := by
    calc
      leftWeight * (2 : K) = (2 : K) * leftWeight := by ring1
      _ = 1 := twiceLeft
  have halfTimesTwo : ((1 : K) / 2) * 2 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 twoNonzero
  have leftIsHalf : leftWeight = (1 : K) / 2 := by
    have differenceTimesTwo : (leftWeight - (1 : K) / 2) * 2 = 0 := by
      calc
        (leftWeight - (1 : K) / 2) * 2 =
            leftWeight * 2 - ((1 : K) / 2) * 2 := by ring1
        _ = 0 := by rw [leftTimesTwo, halfTimesTwo]; ring1
    have differenceZero :=
      eq_zero_of_mul_eq_zero_right twoNonzero differenceTimesTwo
    calc
      leftWeight = (leftWeight - (1 : K) / 2) + (1 : K) / 2 := by ring1
      _ = (1 : K) / 2 := by rw [differenceZero]; ring1
  rw [← combination, weightsEqual, leftIsHalf]
  apply Point.ext <;>
    simp only [affineCombination, midpoint,
      RFAP.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- Theorem 20 (Midpoint), collecting existence, metric value, and
uniqueness in one finite statement. -/
theorem midpoint_theorem [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull : ¬ (lineThrough first second distinct).IsNull) :
    (lineThrough first second distinct).Contains (midpoint first second) ∧
      quadrance (midpoint first second) first =
        quadrance (midpoint first second) second ∧
      quadrance (midpoint first second) first = quadrance first second / 4 ∧
      ∀ point : Point K,
        (lineThrough first second distinct).Contains point →
        quadrance point first = quadrance point second →
        point = midpoint first second := by
  exact ⟨midpoint_on_line first second distinct twoNonzero,
    midpoint_equal_quadrance first second twoNonzero,
    midpoint_quadrance first second twoNonzero,
    fun point onLine equalQuadrances =>
      midpoint_unique_of_equal_quadrance first second point distinct
        twoNonzero sideNonNull onLine equalQuadrances⟩

/-- Theorem 21 (Parallelogram quadrance): opposite sides of a nondegenerate
parallelogram have equal quadrance. -/
theorem parallelogram_quadrance [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    quadrance first second = quadrance third fourth ∧
      quadrance second third = quadrance fourth first := by
  rcases parallelogram_coordinate_sums first second third fourth
    twoNonzero determinantNonzero parallelSides
      with ⟨xSums, ySums⟩
  constructor
  · unfold quadrance
    calc
      (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
          (fourth.x - third.x) ^ 2 + (fourth.y - third.y) ^ 2 := by
            rw [show second.x - first.x = third.x - fourth.x by
              calc
                second.x - first.x = third.x - fourth.x +
                    ((second.x + fourth.x) - (first.x + third.x)) := by ring1
                _ = third.x - fourth.x := by rw [← xSums]; ring1]
            rw [show second.y - first.y = third.y - fourth.y by
              calc
                second.y - first.y = third.y - fourth.y +
                    ((second.y + fourth.y) - (first.y + third.y)) := by ring1
                _ = third.y - fourth.y := by rw [← ySums]; ring1]
            ring1
      _ = (fourth.x - third.x) ^ 2 + (fourth.y - third.y) ^ 2 := rfl
  · unfold quadrance
    rw [show third.x - second.x = fourth.x - first.x by
      calc
        third.x - second.x = fourth.x - first.x +
            ((first.x + third.x) - (second.x + fourth.x)) := by ring1
        _ = fourth.x - first.x := by rw [xSums]; ring1]
    rw [show third.y - second.y = fourth.y - first.y by
      calc
        third.y - second.y = fourth.y - first.y +
            ((first.y + third.y) - (second.y + fourth.y)) := by ring1
        _ = fourth.y - first.y := by rw [ySums]; ring1]
    ring1

/-- Archimedes' symmetric polynomial. -/
def archimedesFunction (a b c : K) : K :=
  (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2)

/-- The coordinate identity underlying the Triple quad formula. -/
theorem archimedes_quadrance_identity
    (first second third : Point K) :
    archimedesFunction
        (quadrance second third)
        (quadrance first third)
        (quadrance first second) =
      4 * pointDeterminant first second third ^ 2 := by
  unfold archimedesFunction quadrance pointDeterminant
  ring1

/-- Theorem 22 (Triple quad formula), valid over every explicit field of
characteristic other than two. -/
theorem triple_quad_formula [Nontrivial K] [DecidableEq K]
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    archimedesFunction
        (quadrance second third)
        (quadrance first third)
        (quadrance first second) = 0 ↔
      Collinear first second third := by
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  constructor
  · intro tripleQuad
    apply (collinear_iff_pointDeterminant_eq_zero first second third).2
    by_cases determinantZero : pointDeterminant first second third = 0
    · exact determinantZero
    · have squareNonzero : pointDeterminant first second third ^ 2 ≠ 0 := by
        simpa [pow_two] using
          RFAP.ExplicitField.mul_ne_zero determinantZero determinantZero
      have productNonzero :=
        RFAP.ExplicitField.mul_ne_zero fourNonzero squareNonzero
      apply False.elim
      apply productNonzero
      calc
        4 * pointDeterminant first second third ^ 2 =
            archimedesFunction
              (quadrance second third)
              (quadrance first third)
              (quadrance first second) :=
                (archimedes_quadrance_identity first second third).symm
        _ = 0 := tripleQuad
  · intro collinear
    have determinantZero :=
      (collinear_iff_pointDeterminant_eq_zero first second third).1 collinear
    rw [archimedes_quadrance_identity, determinantZero]
    ring1

/-- Theorem 23 (Pythagoras): the quadrance relation is equivalent to
perpendicularity at the third vertex. -/
theorem pythagoras_iff_perpendicular [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    quadrance second third + quadrance first third = quadrance first second ↔
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct) := by
  have identity :
      quadrance second third + quadrance first third - quadrance first second =
        2 * ((first.y - third.y) * (second.y - third.y) +
          (third.x - first.x) * (third.x - second.x)) := by
    unfold quadrance
    ring1
  constructor
  · intro pythagoras
    have productZero :
        (2 : K) * ((first.y - third.y) * (second.y - third.y) +
          (third.x - first.x) * (third.x - second.x)) = 0 := by
      calc
        (2 : K) * ((first.y - third.y) * (second.y - third.y) +
            (third.x - first.x) * (third.x - second.x)) =
          quadrance second third + quadrance first third -
            quadrance first second := identity.symm
        _ = 0 := by rw [pythagoras]; ring1
    have dotZero :=
      eq_zero_of_mul_eq_zero_left twoNonzero productZero
    unfold Line.Perpendicular lineThrough
    exact dotZero
  · intro perpendicular
    unfold Line.Perpendicular lineThrough at perpendicular
    calc
      quadrance second third + quadrance first third =
          quadrance first second +
            2 * ((first.y - third.y) * (second.y - third.y) +
              (third.x - first.x) * (third.x - second.x)) := by
                calc
                  quadrance second third + quadrance first third =
                      (quadrance second third + quadrance first third -
                        quadrance first second) + quadrance first second := by ring1
                  _ = 2 * ((first.y - third.y) * (second.y - third.y) +
                        (third.x - first.x) * (third.x - second.x)) +
                      quadrance first second := by rw [identity]
                  _ = quadrance first second +
                      2 * ((first.y - third.y) * (second.y - third.y) +
                        (third.x - first.x) * (third.x - second.x)) := by ring1
      _ = quadrance first second := by rw [perpendicular]; ring1

end DivineProportions
