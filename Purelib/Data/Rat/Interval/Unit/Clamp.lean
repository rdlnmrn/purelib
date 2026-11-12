module

public import Purelib.Data.Rat.Interval.Unit
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Executable projection to the rational unit interval

The original rational comparisons select either endpoint or the supplied
interior value. Direct ordered differences give the squared nonexpansive
bound, including both endpoints and both input orientations.
-/

namespace Purelib.Data.Rat.Interval.Unit

open Purelib.Data.Rat.Fraction

public section

/-- Clip one original rational to the closed unit interval using two finite comparisons. -/
@[expose] def clamp (value : Rational) : Rational :=
  if value ≤ 0 then 0 else if 1 ≤ value then 1 else value

/-- The clipped rational always belongs to the same closed unit interval. -/
theorem clamp_inside (value : Rational) : 0 ≤ clamp value ∧ clamp value ≤ 1 := by
  by_cases lower : value ≤ 0
  · unfold clamp
    rewrite [if_pos lower]
    exact ⟨Order.Basic.le_refl _, (by decide +kernel)⟩
  · by_cases upper : 1 ≤ value
    · unfold clamp
      rewrite [if_neg lower, if_pos upper]
      exact ⟨(by decide +kernel), Order.Basic.le_refl _⟩
    · unfold clamp
      rewrite [if_neg lower, if_neg upper]
      exact ⟨(Order.Basic.le_total 0 value).resolve_right lower,
        (Order.Basic.le_total value 1).resolve_right upper⟩

/-- Clipping an already admitted rational preserves its complete canonical value. -/
theorem clamp_eq {value : Rational} (inside : 0 ≤ value ∧ value ≤ 1) : clamp value = value := by
  by_cases lower : value ≤ 0
  · have same : value = 0 := lower.antisymm inside.1
    unfold clamp
    rewrite [if_pos lower]
    exact same.symm
  · by_cases upper : 1 ≤ value
    · have same : value = 1 := inside.2.antisymm upper
      unfold clamp
      rewrite [if_neg lower, if_pos upper]
      exact same.symm
    · unfold clamp
      rewrite [if_neg lower, if_neg upper]
      rfl

end

/-- Clipping two ordered inputs preserves the order and does not increase their displayed difference. -/
private theorem ordered_difference {left right : Rational} (ordered : left ≤ right) :
    0 ≤ clamp right - clamp left ∧ clamp right - clamp left ≤ right - left := by
  by_cases rightLow : right ≤ 0
  · have leftLow : left ≤ 0 := ordered.trans rightLow
    unfold clamp
    rewrite [if_pos rightLow, if_pos leftLow, show (0 - 0 : Rational) = 0 by ring1]
    exact ⟨Order.Basic.le_refl _, Order.Arithmetic.sub_nonneg_direct ordered⟩
  · by_cases leftLow : left ≤ 0
    · have widening : right ≤ right - left :=
        (show right - 0 = right by ring1).symm.trans_le
          (Order.Arithmetic.sub_le_sub_left_direct leftLow right)
      by_cases rightHigh : 1 ≤ right
      · unfold clamp
        rewrite [if_neg rightLow, if_pos rightHigh, if_pos leftLow,
          show (1 - 0 : Rational) = 1 by ring1]
        exact ⟨(by decide +kernel), rightHigh.trans widening⟩
      · unfold clamp
        rewrite [if_neg rightLow, if_neg rightHigh, if_pos leftLow,
          show right - 0 = right by ring1]
        exact ⟨(Order.Basic.le_total 0 right).resolve_right rightLow, widening⟩
    · by_cases leftHigh : 1 ≤ left
      · have rightHigh : 1 ≤ right := leftHigh.trans ordered
        unfold clamp
        rewrite [if_neg rightLow, if_pos rightHigh, if_neg leftLow, if_pos leftHigh,
          show (1 - 1 : Rational) = 0 by ring1]
        exact ⟨Order.Basic.le_refl _, Order.Arithmetic.sub_nonneg_direct ordered⟩
      · by_cases rightHigh : 1 ≤ right
        · unfold clamp
          rewrite [if_neg rightLow, if_pos rightHigh, if_neg leftLow, if_neg leftHigh]
          exact ⟨Order.Arithmetic.sub_nonneg_direct
            ((Order.Basic.le_total left 1).resolve_right leftHigh),
            Order.Arithmetic.sub_le_sub_right_direct rightHigh left⟩
        · unfold clamp
          rewrite [if_neg rightLow, if_neg rightHigh, if_neg leftLow, if_neg leftHigh]
          exact ⟨Order.Arithmetic.sub_nonneg_direct ordered, Order.Basic.le_refl _⟩

public section

/-- The original rational clipping operation never increases squared distance. -/
theorem clamp_distance_le (left right : Rational) :
    (clamp left - clamp right) ^ 2 ≤ (left - right) ^ 2 := by
  rcases Order.Basic.le_total left right with ordered | reversed
  · have bounded := ordered_difference ordered
    have squared := Order.Arithmetic.pow_le_pow_direct bounded.1 bounded.2 2
    exact (show (clamp left - clamp right) ^ 2 = (clamp right - clamp left) ^ 2 by ring1).trans_le
      (squared.trans_eq (by ring1))
  · have bounded := ordered_difference reversed
    exact Order.Arithmetic.pow_le_pow_direct bounded.1 bounded.2 2

end

end Purelib.Data.Rat.Interval.Unit
