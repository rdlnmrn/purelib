import DivineProportions.Trigonometry.Spread
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Exercises 6.1--6.2

Exercise 6.1 is proved by cancelling only the displayed non-null and
nonperpendicular denominators.  Exercise 6.2 is a closed constructive-rational
counterexample: two distinct nonperpendicular directions have complementary
spreads with a third line.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by ring1
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel]; ring1

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
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
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-- Exercise 6.1: all six displayed conversions among spread, cross, and
twist, for two lines on which all three ratios are defined. -/
theorem exercise_6_1 [Nontrivial K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull)
    (secondNonNull : ¬ second.IsNull)
    (notPerpendicular : ¬ first.Perpendicular second) :
    let s := spread first second firstNonNull secondNonNull
    let c := cross first second firstNonNull secondNonNull
    let t := twist first second notPerpendicular
    t = s / c ∧
      t = s / (1 - s) ∧
      t = (1 - c) / c ∧
      s = t / (1 + t) ∧
      c = 1 / (1 + t) := by
  dsimp only
  let s := spread first second firstNonNull secondNonNull
  let c := cross first second firstNonNull secondNonNull
  let t := twist first second notPerpendicular
  change
    t = s / c ∧
      t = s / (1 - s) ∧
      t = (1 - c) / c ∧
      s = t / (1 + t) ∧
      c = 1 / (1 + t)
  let determinant := first.a * second.b - second.a * first.b
  let dot := first.a * second.a + first.b * second.b
  let normProduct := lineNorm first * lineNorm second
  have dotNonzero : dot ≠ 0 := by
    exact notPerpendicular
  have dotSquareNonzero : dot ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero dotNonzero dotNonzero
  have normProductNonzero : normProduct ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have crossNonzero : c ≠ 0 := by
    change dot ^ 2 / normProduct ≠ 0
    exact RFAP.ExplicitField.div_ne_zero dotSquareNonzero
      normProductNonzero
  have spreadCross : s + c = 1 := by
    exact spread_add_cross first second firstNonNull secondNonNull
  have twistSpreadCross : t = s / c := by
    apply div_eq_div_of_cross_mul dotSquareNonzero crossNonzero
    change determinant ^ 2 * c = s * dot ^ 2
    unfold s spread c cross
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have oneMinusSpread : 1 - s = c := by
    calc
      1 - s = (s + c) - s := by rw [spreadCross]
      _ = c := by ring1
  have oneMinusCross : 1 - c = s := by
    calc
      1 - c = (s + c) - c := by rw [spreadCross]
      _ = s := by ring1
  have twistSpreadOneMinusSpread : t = s / (1 - s) := by
    calc
      t = s / c := twistSpreadCross
      _ = s / (1 - s) := by rw [oneMinusSpread]
  have twistOneMinusCrossCross : t = (1 - c) / c := by
    calc
      t = s / c := twistSpreadCross
      _ = (1 - c) / c := by rw [oneMinusCross]
  have crossTimesOnePlusTwist : c * (1 + t) = 1 := by
    rw [twistSpreadCross]
    calc
      c * (1 + s / c) = c + (s / c) * c := by ring1
      _ = c + s := by
        rw [RFAP.ExplicitField.div_mul_cancel _ crossNonzero]
      _ = 1 := by rw [add_comm, spreadCross]
  have onePlusTwistNonzero : 1 + t ≠ 0 := by
    intro zero
    have oneNonzero : (1 : K) ≠ 0 := one_ne_zero
    apply oneNonzero
    calc
      (1 : K) = c * (1 + t) := crossTimesOnePlusTwist.symm
      _ = 0 := by rw [zero]; ring1
  have spreadTimesOnePlusTwist : s * (1 + t) = t := by
    apply eq_of_mul_eq_mul_right crossNonzero
    calc
      s * (1 + t) * c = s * (c * (1 + t)) := by ring1
      _ = s := by rw [crossTimesOnePlusTwist, mul_one]
      _ = (s / c) * c :=
        (RFAP.ExplicitField.div_mul_cancel _ crossNonzero).symm
      _ = t * c := by rw [twistSpreadCross]
  have spreadFromTwist : s = t / (1 + t) := by
    apply eq_of_mul_eq_mul_right onePlusTwistNonzero
    calc
      s * (1 + t) = t := spreadTimesOnePlusTwist
      _ = (t / (1 + t)) * (1 + t) :=
        (RFAP.ExplicitField.div_mul_cancel _ onePlusTwistNonzero).symm
  have crossFromTwist : c = 1 / (1 + t) := by
    apply eq_of_mul_eq_mul_right onePlusTwistNonzero
    calc
      c * (1 + t) = 1 := crossTimesOnePlusTwist
      _ = (1 / (1 + t)) * (1 + t) :=
        (RFAP.ExplicitField.div_mul_cancel _ onePlusTwistNonzero).symm
  exact ⟨twistSpreadCross, twistSpreadOneMinusSpread,
    twistOneMinusCrossCross, spreadFromTwist, crossFromTwist⟩

namespace ExerciseSixTwo

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The fixed comparison line with coefficient direction `(0,1)`. -/
def comparison : Line Rational where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (by decide)

/-- First rational direction in the Exercise 6.2 counterexample. -/
def first : Line Rational where
  a := 4
  b := 3
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- Second rational direction in the Exercise 6.2 counterexample. -/
def second : Line Rational where
  a := 3
  b := 4
  c := 0
  direction_nonzero := Or.inl (by decide)

private theorem comparisonNonNull : ¬ comparison.IsNull := by
  unfold comparison Line.IsNull
  decide

private theorem firstNonNull : ¬ first.IsNull := by
  unfold first Line.IsNull
  decide

private theorem secondNonNull : ¬ second.IsNull := by
  unfold second Line.IsNull
  decide

/-- Exercise 6.2: complementary spreads with a third line do not force the
first two lines to be perpendicular.  Here the spreads are `16/25` and
`9/25`, while the coefficient dot product is `24`. -/
theorem exercise_6_2 :
    spread first comparison firstNonNull comparisonNonNull = 16 / 25 ∧
      spread second comparison secondNonNull comparisonNonNull = 9 / 25 ∧
      spread first comparison firstNonNull comparisonNonNull +
          spread second comparison secondNonNull comparisonNonNull = 1 ∧
      ¬ first.Perpendicular second := by
  unfold spread lineNorm first second comparison Line.Perpendicular
  decide

end ExerciseSixTwo

end DivineProportions
