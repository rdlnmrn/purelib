import DivineProportions.Trigonometry.TripleSpread
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 7 rational inequalities

Exercise 7.4 is proved with the explicit order on constructive fractions.
Exercise 7.9, as printed, is false for obtuse triangles; the second section
records a fully executable rational counterexample to both claimed bounds.
-/

namespace DivineProportions

namespace ChapterSevenInequalities

abbrev Rational := RFAP.ConstructiveFraction.Rational

private theorem ratio_eq_of_cross_product
    {K : Type*} [RFAP.ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) * rightDenominator⁻¹ := by
          ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

private theorem half_cube_eq_eighth :
    ((1 : Rational) / 2) * ((1 : Rational) / 2) * ((1 : Rational) / 2) =
      (1 : Rational) / 8 := by
  calc
    ((1 : Rational) / 2) * ((1 : Rational) / 2) * ((1 : Rational) / 2) =
        ((1 * 1 : Rational) / (2 * 2)) * ((1 : Rational) / 2) := by
          exact congrArg (fun value : Rational => value * ((1 : Rational) / 2))
            (RFAP.ConstructiveFraction.div_mul_div_direct 1 2 1 2)
    _ = ((1 * 1) * 1 : Rational) / ((2 * 2) * 2) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = (1 : Rational) / 8 := by decide

/-- A denominator-cleared lower estimate used by the counterexample. -/
private theorem half_le_nat_ratio
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (denominatorAtMostTwiceNumerator :
      (denominator : Rational) ≤ (numerator : Rational) * 2) :
    (1 : Rational) / 2 ≤ numerator / denominator := by
  have twoPositive : (0 : Rational) < 2 := by decide
  have castDenominatorPositive : (0 : Rational) < denominator :=
    RFAP.ConstructiveFraction.natCast_pos_direct denominatorPositive
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    castDenominatorPositive).2
  calc
    ((1 : Rational) / 2) * denominator =
        (denominator : Rational) / 2 := by
          rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
            RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
          rw [one_mul, mul_comm]
    _ ≤ numerator :=
      (RFAP.ConstructiveFraction.div_le_iff_pos twoPositive).2
        denominatorAtMostTwiceNumerator

/-- Exercise 7.4: on constructive rationals, the equal-argument Triple-spread
polynomial is nonnegative exactly up to `3/4`. -/
theorem exercise_7_4 (a : Rational) :
    0 ≤ tripleSpreadFunction a a a ↔ a ≤ (3 : Rational) / 4 := by
  have factorization :
      tripleSpreadFunction a a a = a ^ 2 * (3 - 4 * a) := by
    unfold tripleSpreadFunction
    ring1
  rw [factorization]
  have fourPositive : (0 : Rational) < 4 := by decide
  constructor
  · intro productNonnegative
    by_cases aZero : a = 0
    · rw [aZero]
      decide
    · have squareNonnegative : (0 : Rational) ≤ a ^ 2 :=
        RFAP.ConstructiveFraction.sq_nonneg_direct a
      have squareNonzero : a ^ 2 ≠ 0 := by
        intro squareZero
        exact aZero
          ((RFAP.ConstructiveFraction.sq_eq_zero_direct a).1 squareZero)
      have squarePositive : (0 : Rational) < a ^ 2 :=
        lt_of_le_of_ne squareNonnegative (Ne.symm squareNonzero)
      have factorNonnegative : (0 : Rational) ≤ 3 - 4 * a := by
        by_cases nonnegative : (0 : Rational) ≤ 3 - 4 * a
        · exact nonnegative
        · have negative : 3 - 4 * a < (0 : Rational) :=
            lt_of_not_ge nonnegative
          have productNegative :=
            RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
              squarePositive negative
          exact ((not_lt_of_ge productNonnegative) productNegative).elim
      apply (RFAP.ConstructiveFraction.le_div_iff_pos fourPositive).2
      have scaled : 4 * a ≤ (3 : Rational) :=
        RFAP.ConstructiveFraction.le_of_sub_nonneg_direct factorNonnegative
      calc
        a * 4 = 4 * a := by ring1
        _ ≤ 3 := scaled
  · intro upperBound
    have scaled : a * 4 ≤ (3 : Rational) :=
      (RFAP.ConstructiveFraction.le_div_iff_pos fourPositive).1 upperBound
    have factorNonnegative : (0 : Rational) ≤ 3 - 4 * a := by
      have raw := RFAP.ConstructiveFraction.sub_nonneg_direct scaled
      calc
        (0 : Rational) ≤ 3 - a * 4 := raw
        _ = 3 - 4 * a := by ring1
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct a) factorNonnegative

namespace ExerciseSevenNineCounterexample

/-- A thin, non-collinear rational triangle. -/
def firstPoint : Point Rational := ⟨0, 0⟩
def secondPoint : Point Rational := ⟨1, 0⟩
def thirdPoint : Point Rational := ⟨2, 1⟩

/-- Side through the second and third points. -/
def firstLine : Line Rational where
  a := 1
  b := -1
  c := -1
  direction_nonzero := Or.inl (by decide)

/-- Side through the first and third points. -/
def secondLine : Line Rational where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- Side through the first and second points. -/
def thirdLine : Line Rational where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (by decide)

theorem firstLine_nonNull : ¬ firstLine.IsNull := by
  unfold Line.IsNull firstLine
  decide

theorem secondLine_nonNull : ¬ secondLine.IsNull := by
  unfold Line.IsNull secondLine
  decide

theorem thirdLine_nonNull : ¬ thirdLine.IsNull := by
  unfold Line.IsNull thirdLine
  decide

/-- The displayed points really form a non-collinear triangle and the three
displayed lines are its sides. -/
theorem triangle_certificate :
    pointDeterminant firstPoint secondPoint thirdPoint ≠ 0 ∧
      firstLine.Contains secondPoint ∧ firstLine.Contains thirdPoint ∧
      secondLine.Contains firstPoint ∧ secondLine.Contains thirdPoint ∧
      thirdLine.Contains firstPoint ∧ thirdLine.Contains secondPoint := by
  unfold pointDeterminant Line.Contains firstPoint secondPoint thirdPoint
    firstLine secondLine thirdLine
  exact ⟨by decide, by ring1, by ring1, by ring1, by ring1, by ring1, by ring1⟩

theorem cross_values :
    cross secondLine thirdLine secondLine_nonNull thirdLine_nonNull =
        (4 : Rational) / 5 ∧
      cross firstLine thirdLine firstLine_nonNull thirdLine_nonNull =
        (1 : Rational) / 2 ∧
      cross firstLine secondLine firstLine_nonNull secondLine_nonNull =
        (9 : Rational) / 10 := by
  constructor
  · unfold cross
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero secondLine_nonNull thirdLine_nonNull)
      (rational_natCast_nonzero (by decide : 5 ≠ 0))
    unfold secondLine thirdLine
    ring1
  constructor
  · unfold cross
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero firstLine_nonNull thirdLine_nonNull)
      (rational_natCast_nonzero (by decide : 2 ≠ 0))
    unfold firstLine thirdLine
    ring1
  · unfold cross
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero firstLine_nonNull secondLine_nonNull)
      (rational_natCast_nonzero (by decide : 10 ≠ 0))
    unfold firstLine secondLine
    ring1

/-- Exercise 7.9's claimed product bound fails on the rational triangle. -/
theorem product_bound_fails :
    ¬ (cross secondLine thirdLine secondLine_nonNull thirdLine_nonNull *
          cross firstLine thirdLine firstLine_nonNull thirdLine_nonNull *
          cross firstLine secondLine firstLine_nonNull secondLine_nonNull ≤
        (1 : Rational) / 64) := by
  rw [cross_values.1, cross_values.2.1, cross_values.2.2]
  intro claimedBound
  have firstHalf : (1 : Rational) / 2 ≤ 4 / 5 :=
    half_le_nat_ratio 4 5 (by decide) (by decide)
  have secondHalf : (1 : Rational) / 2 ≤ 1 / 2 := le_rfl
  have thirdHalf : (1 : Rational) / 2 ≤ 9 / 10 :=
    half_le_nat_ratio 9 10 (by decide) (by decide)
  have halfNonnegative : (0 : Rational) ≤ (1 : Rational) / 2 := by decide
  have firstNonnegative : (0 : Rational) ≤ 4 / 5 :=
    halfNonnegative.trans firstHalf
  have secondNonnegative : (0 : Rational) ≤ 1 / 2 :=
    halfNonnegative.trans secondHalf
  have firstTwo :
      ((1 : Rational) / 2) * ((1 : Rational) / 2) ≤
        (4 / 5) * (1 / 2) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct firstHalf secondHalf
      halfNonnegative firstNonnegative
  have firstTwoNonnegative : (0 : Rational) ≤ (4 / 5) * (1 / 2) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct firstNonnegative
      secondNonnegative
  have productLower :
      ((1 : Rational) / 2) * ((1 : Rational) / 2) * ((1 : Rational) / 2) ≤
        (4 / 5) * (1 / 2) * (9 / 10) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct firstTwo thirdHalf
      halfNonnegative firstTwoNonnegative
  have strictConstant :
      (1 : Rational) / 64 <
        ((1 : Rational) / 2) * ((1 : Rational) / 2) * ((1 : Rational) / 2) := by
    rw [half_cube_eq_eighth]
    have sixtyFourPositive : (0 : Rational) < 64 :=
      RFAP.ConstructiveFraction.natCast_pos_direct (by decide)
    have eightNonzero : (8 : Rational) ≠ 0 :=
      rational_natCast_nonzero (by decide)
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos sixtyFourPositive).2
    calc
      (1 : Rational) < 8 :=
        RFAP.ConstructiveFraction.natCast_lt_direct
          (show (1 : Nat) < 8 from by decide)
      _ = ((1 : Rational) / 8) * 64 := by
        calc
          (8 : Rational) = (((1 : Rational) / 8) * 8) * 8 := by
            rw [RFAP.ExplicitField.div_mul_cancel 1 eightNonzero]
            ring1
          _ = ((1 : Rational) / 8) * 64 := by ring1
  exact (not_lt_of_ge claimedBound) (strictConstant.trans_le productLower)

/-- Exercise 7.9's claimed upper sum bound fails on the same triangle. -/
theorem sum_bound_fails :
    ¬ (cross secondLine thirdLine secondLine_nonNull thirdLine_nonNull +
          cross firstLine thirdLine firstLine_nonNull thirdLine_nonNull +
          cross firstLine secondLine firstLine_nonNull secondLine_nonNull ≤
        (5 : Rational) / 4) := by
  rw [cross_values.1, cross_values.2.1, cross_values.2.2]
  intro claimedBound
  have firstHalf : (1 : Rational) / 2 ≤ 4 / 5 :=
    half_le_nat_ratio 4 5 (by decide) (by decide)
  have secondHalf : (1 : Rational) / 2 ≤ 1 / 2 := le_rfl
  have thirdHalf : (1 : Rational) / 2 ≤ 9 / 10 :=
    half_le_nat_ratio 9 10 (by decide) (by decide)
  have sumLower :
      (1 : Rational) / 2 + (1 : Rational) / 2 + (1 : Rational) / 2 ≤
        4 / 5 + 1 / 2 + 9 / 10 :=
    RFAP.ConstructiveFraction.add_le_add_direct
      (RFAP.ConstructiveFraction.add_le_add_direct firstHalf secondHalf)
      thirdHalf
  have strictConstant :
      (5 : Rational) / 4 <
        (1 : Rational) / 2 + (1 : Rational) / 2 + (1 : Rational) / 2 := by
    decide
  exact (not_lt_of_ge claimedBound) (strictConstant.trans_le sumLower)

end ExerciseSevenNineCounterexample

end ChapterSevenInequalities

end DivineProportions
