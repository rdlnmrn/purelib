import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.SpreadPolynomial
import DivineProportions.Trigonometry.Quadrea
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 7 worked examples

This module records the exact rational calculation of Example 7.2 and the
fully executable finite-field calculation of Example 7.3.
-/

namespace DivineProportions

namespace ChapterSevenExamples

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
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

namespace ExampleSevenTwo

def point₁ : Point Rational := ⟨1, 1⟩
def point₂ : Point Rational := ⟨5, 2⟩
def point₃ : Point Rational := ⟨3, -1⟩

/-- Line `A₂A₃`. -/
def line₁ : Line Rational where
  a := 3
  b := -2
  c := -11
  direction_nonzero := Or.inl (by decide)

/-- Line `A₁A₃`. -/
def line₂ : Line Rational where
  a := 2
  b := 2
  c := -4
  direction_nonzero := Or.inl (by decide)

/-- Line `A₁A₂`. -/
def line₃ : Line Rational where
  a := -1
  b := 4
  c := -3
  direction_nonzero := Or.inl (by decide)

theorem line_incidence :
    line₁.Contains point₂ ∧ line₁.Contains point₃ ∧
      line₂.Contains point₁ ∧ line₂.Contains point₃ ∧
      line₃.Contains point₁ ∧ line₃.Contains point₂ := by
  unfold Line.Contains line₁ line₂ line₃ point₁ point₂ point₃
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1⟩

theorem quadrance_values :
    quadrance point₂ point₃ = 13 ∧
      quadrance point₁ point₃ = 8 ∧
      quadrance point₁ point₂ = 17 := by
  unfold quadrance point₁ point₂ point₃
  exact ⟨by ring1, by ring1, by ring1⟩

theorem quadrea_value : quadrea point₁ point₂ point₃ = 400 := by
  unfold quadrea archimedesFunction quadrance point₁ point₂ point₃
  ring1

theorem line₁_nonNull : ¬ line₁.IsNull := by
  unfold Line.IsNull line₁
  decide

theorem line₂_nonNull : ¬ line₂.IsNull := by
  unfold Line.IsNull line₂
  decide

theorem line₃_nonNull : ¬ line₃.IsNull := by
  unfold Line.IsNull line₃
  decide

theorem spread_values :
    spread line₂ line₃ line₂_nonNull line₃_nonNull =
        (25 : Rational) / 34 ∧
      spread line₁ line₃ line₁_nonNull line₃_nonNull =
        (100 : Rational) / 221 ∧
      spread line₁ line₂ line₁_nonNull line₂_nonNull =
        (25 : Rational) / 26 := by
  constructor
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero line₂_nonNull line₃_nonNull)
      (rational_natCast_nonzero (by decide : 34 ≠ 0))
    unfold line₂ line₃
    ring1
  constructor
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero line₁_nonNull line₃_nonNull)
      (rational_natCast_nonzero (by decide : 221 ≠ 0))
    unfold line₁ line₃
    ring1
  · unfold spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero line₁_nonNull line₂_nonNull)
      (rational_natCast_nonzero (by decide : 26 ≠ 0))
    unfold line₁ line₂
    ring1

theorem cross_values :
    cross line₂ line₃ line₂_nonNull line₃_nonNull =
        (9 : Rational) / 34 ∧
      cross line₁ line₃ line₁_nonNull line₃_nonNull =
        (121 : Rational) / 221 ∧
      cross line₁ line₂ line₁_nonNull line₂_nonNull =
        (1 : Rational) / 26 := by
  constructor
  · unfold cross
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero line₂_nonNull line₃_nonNull)
      (rational_natCast_nonzero (by decide : 34 ≠ 0))
    unfold line₂ line₃
    ring1
  constructor
  · unfold cross
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero line₁_nonNull line₃_nonNull)
      (rational_natCast_nonzero (by decide : 221 ≠ 0))
    unfold line₁ line₃
    ring1
  · unfold cross
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero line₁_nonNull line₂_nonNull)
      (rational_natCast_nonzero (by decide : 26 ≠ 0))
    unfold line₁ line₂
    ring1

/-- The two chapter formulas evaluated on the displayed rational triangle. -/
theorem triple_formulas :
    let s₁ := spread line₂ line₃ line₂_nonNull line₃_nonNull
    let s₂ := spread line₁ line₃ line₁_nonNull line₃_nonNull
    let s₃ := spread line₁ line₂ line₁_nonNull line₂_nonNull
    let c₁ := cross line₂ line₃ line₂_nonNull line₃_nonNull
    let c₂ := cross line₁ line₃ line₁_nonNull line₃_nonNull
    let c₃ := cross line₁ line₂ line₁_nonNull line₂_nonNull
    (s₁ + s₂ + s₃) ^ 2 =
        2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ ∧
      (c₁ + c₂ + c₃ - 1) ^ 2 = 4 * c₁ * c₂ * c₃ := by
  dsimp only
  exact ⟨triple_spread_formula line₁ line₂ line₃ line₁_nonNull
      line₂_nonNull line₃_nonNull,
    triple_cross_formula line₁ line₂ line₃ line₁_nonNull line₂_nonNull
      line₃_nonNull⟩

end ExampleSevenTwo

namespace ExampleSevenThree

abbrev F₁₁ := FieldEleven.Element

def point₁ : Point F₁₁ := ⟨1, 1⟩
def point₂ : Point F₁₁ := ⟨3, 4⟩
def point₃ : Point F₁₁ := ⟨9, 5⟩

def line₁ : Line F₁₁ where
  a := 10
  b := 6
  c := 1
  direction_nonzero := Or.inl (by decide)

def line₂ : Line F₁₁ where
  a := 1
  b := 9
  c := 1
  direction_nonzero := Or.inl (by decide)

def line₃ : Line F₁₁ where
  a := 8
  b := 2
  c := 1
  direction_nonzero := Or.inl (by decide)

theorem line₁_nonNull : ¬ line₁.IsNull := by
  unfold Line.IsNull line₁
  decide

theorem line₂_nonNull : ¬ line₂.IsNull := by
  unfold Line.IsNull line₂
  decide

theorem line₃_nonNull : ¬ line₃.IsNull := by
  unfold Line.IsNull line₃
  decide

theorem line_incidence :
    line₁.Contains point₂ ∧ line₁.Contains point₃ ∧
      line₂.Contains point₁ ∧ line₂.Contains point₃ ∧
      line₃.Contains point₁ ∧ line₃.Contains point₂ := by
  unfold Line.Contains line₁ line₂ line₃ point₁ point₂ point₃
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem quadrance_values :
    quadrance point₂ point₃ = 4 ∧
      quadrance point₁ point₃ = 3 ∧
      quadrance point₁ point₂ = 2 := by
  exact ⟨by decide, by decide, by decide⟩

theorem quadrea_value : quadrea point₁ point₂ point₃ = 1 := by
  decide

theorem spread_values :
    spread line₂ line₃ line₂_nonNull line₃_nonNull = 6 ∧
      spread line₁ line₃ line₁_nonNull line₃_nonNull = 10 ∧
      spread line₁ line₂ line₁_nonNull line₂_nonNull = 3 := by
  exact ⟨by decide, by decide, by decide⟩

/-- The complete executable calculation in `F₁₁`. -/
theorem example_7_3 :
    line₁.Contains point₂ ∧ line₁.Contains point₃ ∧
      line₂.Contains point₁ ∧ line₂.Contains point₃ ∧
      line₃.Contains point₁ ∧ line₃.Contains point₂ ∧
      quadrance point₂ point₃ = 4 ∧
      quadrance point₁ point₃ = 3 ∧
      quadrance point₁ point₂ = 2 ∧
      quadrea point₁ point₂ point₃ = 1 ∧
      spread line₂ line₃ line₂_nonNull line₃_nonNull = 6 ∧
      spread line₁ line₃ line₁_nonNull line₃_nonNull = 10 ∧
      spread line₁ line₂ line₁_nonNull line₂_nonNull = 3 := by
  exact ⟨line_incidence.1, line_incidence.2.1, line_incidence.2.2.1,
    line_incidence.2.2.2.1, line_incidence.2.2.2.2.1,
    line_incidence.2.2.2.2.2, quadrance_values.1,
    quadrance_values.2.1, quadrance_values.2.2, quadrea_value,
    spread_values.1, spread_values.2.1, spread_values.2.2⟩

theorem triple_spread_value :
    let s₁ := spread line₂ line₃ line₂_nonNull line₃_nonNull
    let s₂ := spread line₁ line₃ line₁_nonNull line₃_nonNull
    let s₃ := spread line₁ line₂ line₁_nonNull line₂_nonNull
    (s₁ + s₂ + s₃) ^ 2 = 9 ∧
      2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ = 9 := by
  decide

end ExampleSevenThree

end ChapterSevenExamples

end DivineProportions
